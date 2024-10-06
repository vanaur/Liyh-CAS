namespace Liyh.Kernel

[<AutoOpen>]
module rec Atomic =
    open System
    open System.Linq
    open ByteDev.Encoding

    exception public UnknownSymbolicMatchException of Symbol
    exception public UnboundArgumentNameException of string list * Symbol

    let private symbolToString { atom = atom; attributes = attributes } =
        sprintf "%s%s" (string atom)
        <| match attributes with
           | [] -> ""
           | xs -> sprintf "[%s]" (String.Join(", ", List.map snd xs))

    /// Attribute type with no effect, only allowing to see directly that a type is symbolic.
    type public Symbolic() =
        inherit Attribute()

    /// An atom is a basic building block for symbolic entities, making it possible to construct an identifier,
    /// a numerical constant or simple text.
    [<Symbolic; StructuralEquality; StructuralComparison>]
    type public Atom =
        | Identifier of name: string
        | Const of cst: Constant
        | Text of text: string

        override this.ToString() =
            match this with
            | Identifier name -> name
            | Const cst -> string cst
            | Text text -> sprintf "%A" text

    let inline private hashSymbol { atom = atom; attributes = attributes } =
        HashCode.Combine(atom, attributes)

    /// A symbol essentially consists of an atom to which attributes are assigned. This is what all Liyh symbolic
    /// elements are represented with, although specialised representations are used in practice. A symbol is therefore
    /// the abstract representation used to communicate between the various symbolic representations and with the user.
    [<Symbolic; StructuralEquality; StructuralComparison>]
    type public Symbol =
        { atom: Atom
          attributes: (string * Symbol) list }

        override this.ToString() = symbolToString this

        interface ISymbolic with
            member this.ToSymbolic() = this
            member this.ToLatex() = None
            member this.ToLatexOrString() = string this
            member this.Hash = hashSymbol this

    /// Retrieves the arguments of the attributes of the given symbol, i.e. without parameter name.
    let inline public getArgsOnly (attributes: (string * Symbol) list) =
        (List.unzip >> snd) attributes

    /// Represents a single atom as a symbol.
    let inline public atom (atom: Atom) =
        { atom = atom; attributes = [] }

    /// Represents the symbolic interface. A type is ‘Symbolic’ if it implements this interface,
    /// in other words it has the members
    /// 
    ///  - `ToSymbolic: unit -> Symbol` which converts the type into a general symbolic representation.
    ///  - `ToLatex: unit -> string option` which allows latex rendering when available and possible.
    ///  - `ToLatexOrString: unit -> string` which renders latex when available and possible, otherwise return a string.
    ///  - `Hash: int` which yields the hash-code of the symbol.
    /// 
    /// The most important member being the `ToSymbolic` one, the others being of a practical nature..
    [<Serializable>]
    type public ISymbolic =
        abstract member ToSymbolic: unit -> Symbol
        abstract member ToLatex: unit -> string option
        abstract member ToLatexOrString: unit -> string
        abstract member Hash: int

    (* Helpers for ISymbolic interface. *)

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

/// Implements an elementary parser for symbols. It is not currently used in Liyh in practice, but may
/// be useful for an external source wishing to use Liyh's capabilities.
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

    let private pAtom =
        choice [ pIdentifier |>> Atom.Identifier; pConst; pText ]

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

