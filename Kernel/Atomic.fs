namespace Liyh.Kernel

[<AutoOpen>]
module rec Atomic =
    open System
    open System.Linq
    open ByteDev.Encoding

    exception public UnknownSymbolicMatchException of Symbol
    exception public UnboundArgumentNameException of string list * Symbol

    let rec private showIndented (lvl: int) { atom = atom; attributes = attributes } =
        let ind lvl = String(' ', lvl)

        sprintf "%s%s" (string atom)
        <| match attributes with
           | [] -> ""
           | xs ->
               sprintf "\n%s" (ind lvl)
               + String.Join(sprintf "\n%s" (ind (lvl)), List.map (showIndented (lvl + 1)) (List.map snd xs))

    let private symbolToString { atom = atom; attributes = attributes } =
        sprintf "%s%s" (string atom)
        <| match attributes with
           | [] -> ""
           | xs -> sprintf "[%s]" (String.Join(", ", List.map snd xs))

    /// Attribute type with no effect, only allowing to see directly that a type is symbolic.
    type public Symbolic() = inherit Attribute()

    [<Struct; Symbolic>]
    type public Atom =
        | Identifier of name: string
        | Const of cst: Constant
        | Text of text: string
        | ReAny of any: string

        override this.ToString() =
            match this with
            | Identifier name -> name
            | Const cst -> string cst
            | Text text -> sprintf "%A" text
            | ReAny any -> sprintf "?%s" any

    let inline private hashSymbol { atom = atom; attributes = attributes } =
        HashCode.Combine(atom, attributes)

    [<NoComparison; NoEquality; Symbolic>]
    type public Symbol =
        { atom: Atom
          attributes: (string * Symbol) list }

        override this.ToString() = symbolToString this
        member public this.ShowIndented() = showIndented 0 this

        interface ISymbolic with
            member this.ToSymbolic() = this
            member this.ToLatex() = None
            member this.ToLatexOrString() = string this
            member this.Hash = hashSymbol this

    let inline public getArgsOnly (attributes: (string * Symbol) list) = (List.unzip >> snd) attributes

    let inline public atom (atom: Atom) = { atom = atom; attributes = [] }

    let inline public (|Symbol|) { atom = atom; attributes = attributes } =
        Symbol(atom, (List.unzip >> snd) attributes)

    let inline public (|Atom|_|) { atom = atom; attributes = attributes } =
        if List.isEmpty attributes then Some(Atom atom) else None

    /// The "universal symbolic representation" linking all Liyh's different symbolic representations.
    [<Serializable>]
    type public ISymbolic =
        abstract member ToSymbolic: unit -> Symbol
        abstract member ToLatex: unit -> string option
        abstract member ToLatexOrString: unit -> string
        abstract member Hash: int

    let inline public toSymbolic (x: ISymbolic) = x.ToSymbolic()
    let inline public toLatex (x: ISymbolic) = x.ToLatex()
    let inline public toLatexValue (x: ISymbolic) = x.ToLatex().Value
    let inline public toLatexOrString (x: ISymbolic) = x.ToLatexOrString()

    let private encoder = new Base64.Base64Encoder()
    let private serializer = new Serialization.Serializer(encoder);

    /// Encodes the given symbol in the universal serialized symbolic representation.
    let public serialize : ISymbolic -> string = toSymbolic >> serializer.Serialize

    /// Decodes the given text in the universal symbolic representation.
    let public deserialize : string -> Symbol = serializer.Deserialize

    /// Gets the attributes of the given symbol in the given argument order. This requires that the attributes
    /// are named correctly and not null, and that the list of names matches the list of attribute names.
    /// This function can throw the `UnboundArgumentNameException` exception otherwise.
    let public getArgumentsByName (names: string list) (symbol: Symbol) =
        let arguments = symbol.attributes

        if List.length arguments <> List.length names then
            raise (UnboundArgumentNameException (names, symbol))

        let inline selector x =
            Option.defaultWith
                (fun _ -> raise (UnboundArgumentNameException (names, symbol)))
                (List.tryFindIndex (( = ) (fst x)) names)

        arguments.OrderBy selector
        |> Seq.toList
        |> List.map snd


[<RequireQualifiedAccess>]
module AtomicParser =
    open FParsec
    open System

    let private pIdentifier =

        let isAsciiIdStart = isAsciiLetter

        let isAsciiIdContinue c =
            isDigit c || c = ''' || isAsciiIdStart c

        identifier (
            IdentifierOptions(
                isAsciiIdStart = isAsciiIdStart,
                isAsciiIdContinue = isAsciiIdContinue,
                normalization = Text.NormalizationForm.FormKD,
                normalizeBeforeValidation = true,
                allowAllNonAsciiCharsInPreCheck = true,
                invalidCharMessage = "The identifier contains an invalid character"
            )
        )

    let private pNumLit =
        let numFmt =
            NumberLiteralOptions.AllowPlusSign
            ||| NumberLiteralOptions.AllowFraction
            ||| NumberLiteralOptions.AllowExponent

        numberLiteral numFmt "number"

    let private pConst =
        pNumLit |>> fun n -> Atom.Const (Constant(double n.String))

    let private pText =
        let unescape = function
            | 'n' -> '\n'
            | 'r' -> '\r'
            | 't' -> '\t'
            | '"' -> '\"'
            | ''' -> '\''
            | c -> c

        let escape = skipChar '\\' >>. (anyOf "\\nrt\"" |>> unescape) <?> ""

        let pString1 =
            let nchar = satisfy (fun c -> c <> '\\' && c <> '"')
            between (skipChar '"') (skipChar '"' <?> "the end of the string") (manyChars (nchar <|> escape))

        let pString2 =
            let nchar = satisfy (fun c -> c <> '\\' && c <> ''')
            between (skipChar ''') (skipChar ''' <?> "the end of the string") (manyChars (nchar <|> escape))

        choice [ pString1; pString2 ] <?> "character string" |>> Atom.Text

    let private pReAny = pipe2 (pstring "?") pIdentifier (fun _ any -> Atom.ReAny any)

    let private pAtom =
        choice [ pIdentifier |>> Atom.Identifier; pConst; pText; pReAny ]

    let private pSymbol, pSymbolImpl = createParserForwardedToRef ()

    let private pAttribute () =
        let pAttrName =
            attempt (pipe2 (spaces >>. pIdentifier) (spaces >>. pchar ':') (fun attrName _ -> attrName))

        pipe2 (spaces >>. opt pAttrName) (spaces >>. pSymbol) (fun attrName atom ->
            (match attrName with
             | Some name -> name
             | None -> null),
            atom)

    let private pSymbAttributes =
        (between (pchar '[') (pchar ']') (sepBy (pAttribute ()) (spaces >>. pchar ',')))
        <|>% []

    let private pSymbol' =
        pipe2 (spaces >>. pAtom) (spaces >>. pSymbAttributes) (fun atom attributes ->
            { atom = atom; attributes = attributes })

    pSymbolImpl.Value <- pSymbol'

    /// Parse a symbolic expression.
    let public parseSymb = runParserOnString pSymbol () ""

module Transform =
    open FParsec

    type public Rule =
        { left: Symbol
          right: Symbol
          name: string option
          condition: Symbol option }

        override this.ToString() =
            sprintf
                "%s%s%s -> %s"
                (Option.fold (fun _ a -> sprintf "%A  " a) null this.name)
                (if this.condition.IsSome then
                     sprintf "(ASSUME %s):  " (toLatexOrString this.condition.Value)
                 else
                     "")
                (toLatexOrString this.left)
                (toLatexOrString this.right)

    type public RuleClass =
        { name: string
          rules: Rule list }

        override this.ToString() =
            sprintf
                "%s%s"
                (if isNull this.name then "" else sprintf "class %s:\n" this.name)
                ("  " + System.String.Join("\n  ", List.map string this.rules))

    let inline public (!<) (sym: string) =
        match AtomicParser.parseSymb sym with
        | Success(sym, _, _) -> sym
        | Failure(msg, _, _) -> failwithf "%s" msg

    let inline public (|->) (left: string) (right: string) (name: string) =
        match AtomicParser.parseSymb left, AtomicParser.parseSymb right with
        | Success(left, _, _), Success(right, _, _) ->
            { left = left
              right = right
              name = Option.ofObj name
              condition = None }
        | Failure(msg1, _, _), _ -> failwithf "left error: %s" msg1
        | _, Failure(msg2, _, _) -> failwithf "right error: %s" msg2

    let inline public (?->) (left: string) (right: string) (cond: string) (name: string) =
        match AtomicParser.parseSymb cond with
        | Success(cond, _, _) ->
            { (left |-> right) name with
                condition = Some cond }
        | Failure(msg, _, _) -> failwithf "cond error: %s" msg

    let private sortByGenerality (rules: Rule list) =

        let rec countAny =
            function
            | Atom(ReAny _) -> 1
            | Symbol(_, xs) -> manyCountAny xs

        and folder acc a = acc + countAny a
        and manyCountAny = List.fold folder 0

        let inner { left = left1 } { left = left2 } =
            match left1, left2 with
            | Atom a, Atom b -> compare a b
            | Symbol(ReAny _, _), Symbol(ReAny _, _) -> 0
            | Symbol(ReAny _, _), _ -> 0
            | _, Symbol(ReAny _, _) -> 0
            | Symbol(_, xs), Symbol(_, ys) -> compare (manyCountAny ys) (manyCountAny xs)

        List.sortWith inner rules |> List.rev

    let private doesApply (symbol: Symbol) (rule: Rule) = 0

    let public transform (rules: Rule list) (symbol: Symbol) = 0

    let public reduce (ruleClass: RuleClass) (symbol: Symbol) = 0

    // Add[?a, 0]  -> ?a
    // Add[?a, ?b] -> Add[?b, ?a]
    //
    //      Add[Add[3, 0], Add[0, 4]]
    //  <=> Add[Add[3, 0], Add[4, 0]]
    //  <=> Add[3, 4]
    //
    // Dictionary
    //      Key: Add[?a, 0]     Value: ?a
    //      Key: Add[?a, ?b]    Value: Add[?b, ?a]
    //
    //  (=> Infer    Add[Int, Int] -> Int)

