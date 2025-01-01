namespace Liyh.Language.Syntax

#nowarn "25"
#nowarn "40"

/// The parser of Liyh.
module rec Parser =
    open Liyh.Language.Syntax.Indentation
    open Liyh.Language.Syntax.Location
    open Liyh.Language.Syntax.Cosyn
    open Liyh.Language.Operator.LiyhOperators
    open Liyh.Language.Operator.LiyhUnits
    open Liyh.Internal.DiagnosticKinds
    open Liyh.Internal.Diagnostics
    open System.Collections.Generic
    open System.Linq
    open FParsec

    (* During parsing, some new small rules can be added dynamically by the user, new operators and
       new units can be defined. Thus, we keep these two mutable states which evolve during the parsing
       of a Liyh code. These two states will be kept throughout the evaluation of a program because they
       are modified during the parsing but keep useful information for the continuation. *)

    /// The list of units defined in a program.
    let private unitList = new LiyhUnits()

    /// The list of operators defined in a program.
    let private operatorList = new LiyhOperators<_>()


    (* Useful functions and parsers *)


    /// Checks whether two `Name` define the same qualified name, regardless of position.
    let public compareNames ((xs1, (fname1, _)): Name) ((xs2, (fname2, _)): Name) =
        if (fname1 <> fname2) || (xs1.Length <> xs2.Length) then false
        else (Seq.zip xs1 xs2).All(fun ((s1, _), (s2, _)) -> s1 = s2)

    /// Return the given list with the first item removed.
    let private init xs = List.removeAt (List.length xs - 1) xs

    /// Currying function, apply the given function `f` to the 2-tuple of `a` and `b`.
    let private curry f a b = f (a, b)

    /// Parse white spaces but no newline
    let private whitespaces =
        let ws = manySatisfy (fun c -> c = ' ' || c = '\t') >>% ()
        ws >>? (attempt (lineComment "#") <|> ws)

    /// Parse ':' with spaces.
    let private doubleDot = whitespaces .>>? skipChar ':'

    /// Define a keyword as an skipped string case-insensitive.
    let private keyword = skipStringCI

    /// Returns a new position offset.
    let private adjustPosition offset (pos: Position) =
        Position(pos.StreamName, pos.Index + int64 offset, pos.Line, pos.Column + int64 offset)

    /// From two trees each with a location, retrieve the location that separates the two trees.
    let private getLocFromPoss a b =
        let (_, (pos1, _)) = a
        let (_, (_, pos2)) = b
        pos1, pos2

    /// Apply the parser `p` and keep the location and then apply the function `f` to the result.
    let private (|>>>) (p: Parser<'a, _>) (f: 'a * Location -> _) = pWithLoc p |>> f

    /// Apply the `opt` parser then the `attempt` parser.
    let private optAttempt p = opt (attempt p)

    /// Parse a sequence of `p` separated by `,` and taking care of the
    /// indentation with respect to the given position.
    /// ```
    /// sepBy (atLeast pos p) (attempt (atLeast pos (skipChar ',')))
    /// ```
    let private sepByCommaInd p pos =
        attempt (sepBy (atLeast pos p) (attempt <| atLeast pos (skipChar ',')))
        <|>% []

    /// Same as `sepByCommaInd` but have to parse at least one item.
    let private sepByCommaInd1 p pos =
        attempt (sepBy1 (atLeast pos p) (attempt <| atLeast pos (skipChar ',')))

    /// Like `sepBy` but for anyly `n` times `p`.
    let private sepByArray p sep n =
        let errMsgUnesxpected =
            sprintf "another element from a sequence of %d elements" n

        pipe2 (parray (n - 1) (p .>>? sep)) (p .>>? notFollowedByL sep errMsgUnesxpected) (fun a b ->
            List.ofArray a @ [ b ])

    /// Apply the given parser between `[` and `]`.
    let private betweenHooks p =
        between
            (whitespaces >>. skipChar '[')
            (whitespaces >>. skipChar ']'
             <?> "the end of the parameter list")
            p

    /// Parse a unicode superscript integer exponent.
    let private pUExp =
        let uexps =
            [ '⁰'
              '¹'
              '²'
              '³'
              '⁴'
              '⁵'
              '⁶'
              '⁷'
              '⁸'
              '⁹' ]

        let expConv = function
            | '⁰' -> "0"
            | '¹' -> "1"
            | '²' -> "2"
            | '³' -> "3"
            | '⁴' -> "4"
            | '⁵' -> "5"
            | '⁶' -> "6"
            | '⁷' -> "7"
            | '⁸' -> "8"
            | '⁹' -> "9"

        many1Satisfy (fun c -> List.contains c uexps)
        >>= fun uexp ->

                let sConv (s: string) =
                    int (String.concat "" (seq { for c in s -> expConv c }))

                preturn (int (sConv uexp))

    /// The operator precedence parser.
    let private opp = new OperatorPrecedenceParser<_, _, _>()

    (* Series of utilities for adding and manipulating MixFix (_ ● _), PostFix (_ ●) and PreFix (● _) operators.
    The addition of a unit, such as `7 g` (read 7 grams) is added to the parsing as a PostFix operator and is
    therefore handled here as well. *)

    /// Utility to add a postfix operator.
    let private addPostfixOp opStr prec assoc mapping =
        opp.AddOperator
        <| PostfixOperator(
            opStr,
            getPosition .>> spaces,
            prec,
            assoc,
            (),
            fun opPos x -> mapping (adjustPosition -opStr.Length opPos) x
        )

    /// Utility to add a postfix operator.
    let private postfixMapping (opStr: string) =
        fun opPos expr ->

            let opLoc =
                adjustPosition -opStr.Length opPos, opPos

            match unitList.TryFind opStr with
            | None -> ExprPostFixOpCall((opStr, opLoc), expr), snd expr
            | Some _ -> ExprWithUnit(expr, (opStr, opLoc)), snd expr

    /// Utility to add a prefix operator.
    let private addPrefixOp opStr prec assoc mapping =
        opp.AddOperator
        <| PrefixOperator(
            opStr,
            getPosition .>> spaces,
            prec,
            assoc,
            (),
            fun opPos x -> mapping (adjustPosition -opStr.Length opPos) x
        )

    /// Utility to add a prefix operator.
    let private prefixMapping (opStr: string) =
        fun opPos expr ->

            let opLoc =
                adjustPosition -opStr.Length opPos, opPos

            ExprPrefixOpCall((opStr, opLoc), expr), snd expr

    /// Utility to add an infix operator.
    let private addInfixOp opStr prec assoc mapping =
        opp.AddOperator
        <| InfixOperator(
            opStr,
            getPosition .>> spaces,
            prec,
            assoc,
            (),
            fun opPos l r -> mapping (adjustPosition -opStr.Length opPos) l r
        )

    /// Utility to add an infix operator.
    let private infixMapping (opStr: string) =
        fun opPos left right ->

            let opLoc =
                adjustPosition -opStr.Length opPos, opPos

            ExprBinOpCall((opStr, opLoc), left, right), getLocFromPoss left right

    /// Utility to add (in)equation operator.
    let private equationMapping (eqKind: EquationKind) =
        fun _ left right -> ExprEquation(eqKind, left, right), getLocFromPoss left right


    (* Adding the default operators to the parsing table. *)


    do addInfixOp "=" EqualityPrecedence Associativity.None (equationMapping Eq)
    do addInfixOp "!=" EqualityPrecedence Associativity.None (equationMapping Neq)
    do addInfixOp "<" EqualityPrecedence Associativity.Left (equationMapping Le)
    do addInfixOp "<=" EqualityPrecedence Associativity.Left (equationMapping Leq)
    do addInfixOp ">" EqualityPrecedence Associativity.Left (equationMapping Gr)
    do addInfixOp ">=" EqualityPrecedence Associativity.Left (equationMapping Greq)

    do addInfixOp "+" AdditionPrecedence Associativity.Left (infixMapping "+")
    do addInfixOp "-" SubstractionPrecedence Associativity.Left (infixMapping "-")
    do addInfixOp "*" MultiplicationPrecedence Associativity.Left (infixMapping "*")
    do addInfixOp "/" DivisionPrecedence Associativity.Left (infixMapping "/")
    do addInfixOp "**" ExponentPrecedence Associativity.None (infixMapping "**")
    do addInfixOp "mod" ModuloPrecedence Associativity.Left (infixMapping "mod")

    do addPrefixOp "-" UnitPrecedence true (prefixMapping "-")


    (* Parsing literals. *)


    /// Parse either an integer or a float and return a NumberLiteral with the position.
    let private pNumLit =
        let numFmt =
            NumberLiteralOptions.AllowPlusSign
            ||| NumberLiteralOptions.AllowFraction
            ||| NumberLiteralOptions.AllowExponent

        numberLiteral numFmt "number" |> pWithLoc

    /// Parse either an integer or a float.
    let private pNumber =
        pNumLit
        |>> fun (nlit, loc) ->
                match nlit with
                | n when n.IsInteger -> Integer(int n.String), loc
                | _ -> Float(float nlit.String), loc

    /// Parse a classic string.
    let private pString' =
        let unescape = function
            | 'n' -> '\n'
            | 'r' -> '\r'
            | 't' -> '\t'
            | '"' -> '\"'
            | ''' -> '\''
            | c -> c

        let escape =
            skipChar '\\' >>. (anyOf "\\nrt\"" |>> unescape)
            <?> ""

        let pString1 =
            let nchar = satisfy (fun c -> c <> '\\' && c <> '"')
            between (skipChar '"') (skipChar '"' <?> "the end of the string") (manyChars (nchar <|> escape))

        let pString2 =
            let nchar = satisfy (fun c -> c <> '\\' && c <> ''')
            between (skipChar ''') (skipChar ''' <?> "the end of the string") (manyChars (nchar <|> escape))

        choice [ pString1; pString2 ] <?> "character string"

    /// Parse a classic string literal.
    let private pString =
        pString' |>>> fun (str, loc) -> String str, loc

    /// Parse a multi-line string as a literal.
    let private pMultiLineString =

        let seqOfCharToString (cs: char seq) =
            System.String.Concat(Array.ofSeq cs)

        let rec remAtLeastCol s = function
            | 0 -> s
            | i ->
                match s with
                | ' ' :: tail -> remAtLeastCol tail (i - 1)
                | _ -> s

        parse {
            do! skipString "\"\"\"" .>> skipNewline
            let! pos = getPosition |>> adjustPosition -4
            let! content = manyChars (satisfy (fun c -> c <> '"'))
            do! skipString "\"\"\""

            let until = int pos.Column

            let st =
                content.Split '\n'
                |> Array.map (fun s ->
                    remAtLeastCol (Seq.toList s) until
                    |> seqOfCharToString)
                |> String.concat "\n"

            return String st
        }
        |>>> fun (str, loc) -> str, loc

    /// Parse 'True' or 'False'.
    let private pBoolean =
        pWithLoc
        <| choice [ skipString "True" >>% True
                    skipString "False" >>% False ]

    /// Parse any literal of the language.
    let private pLiteral =
        choice [ pNumber
                 pBoolean
                 pMultiLineString
                 pString ]


    (* Identifiers are valid character sequences (letters + numbers, not starting with a number).
       It is also possible to define a more general identifier which accepts any character or space
       via a pair of quotes. No identifier must correspond to a language keyword. Specific keywords
       such as `associativity` or `priority` are not reserved. *)


    /// List of reserved keywords.
    let private reservedKeywords =
        [ "alias"
          "breakloop"
          "constructor"
          "CurrentVariable"
          "do"
          "else"
          "enumeration"
          "extends"
          "extern"
          "for"
          // "from"
          "if"
          "infinity"
          "in"
          "is"
          "latex"
          "let"
          "mod"
          "namespace"
          "notation"
          "object"
          "or"
          "perform"
          "region"
          "record"
          "return"
          "select"
          "set"
          "then"
          "unit"
          "use"
          "procedure"
          "when"
          "while"
          "with" ]

    /// Parse valid identifier.
    let private pIdentifier' =

        let isAsciiIdStart = isAsciiLetter

        let isAsciiIdContinue c =
            isDigit c || c = ''' || isAsciiIdStart c

        pWithLoc
        <| identifier (
            IdentifierOptions(
                isAsciiIdStart = isAsciiIdStart,
                isAsciiIdContinue = isAsciiIdContinue,
                normalization = System.Text.NormalizationForm.FormKD,
                normalizeBeforeValidation = true,
                //allowAllNonAsciiCharsInPreCheck = true, // conflict with uexp
                invalidCharMessage = "The identifier contains an invalid character"
            )
        )
        >>= fun (id, loc) ->
                match List.contains id reservedKeywords with
                | true -> failf "`[lightskyblue3_1]%s[/]` is a reserved word" id
                | false -> preturn (id, loc)

    /// Parse any character between quotes as a valid identifier.
    let private pQuotedIdentifier =
        pWithLoc (
            skipChar '`'
            >>. many1CharsTill anyChar (skipChar '`')
        )

    /// It is useful to introduce the degree '°' for temperatures or angles as first character of an identifier.
    let private pDegId =
        pipe2 (pWithLoc (pchar '°')) pIdentifier' (fun (_, (p1, _)) (r, (_, p2)) -> sprintf "°%s" r, (p1, p2))

    /// Parse valid identifier.
    let private pIdentifier =
        choiceL
            [ attempt pIdentifier'
              pDegId
              pQuotedIdentifier
              pWithLoc (pstring "_") ]
            "identifier"

    /// Parse a qualified name.
    let private pName =
        sepBy1
            pIdentifier
            (skipChar '.' <?> "name qualification"
             .>>? notFollowedByString "[") // For array access purpose
        |>> fun xs -> (init xs, List.last xs)


    (* Parsing of terms. A term is a unique and constitutive component of an expression involving operators. *)


    /// Parse a literal as an expression.
    let private pExprLiteral =
        attempt pLiteral
        |>> fun (lit, loc) -> ExprLiteral lit, loc

    /// Parse a qualified name as an expression.
    let private pExprName =
        pName |>>> fun (xs, loc) -> ExprName xs, loc

    /// Parse an access to an element of an array à la F#.
    let private pTableAccess =
        parse {
            let! pos = getPosition
            do! any pos (skipString ".[") <?> "array access operator"

            let! access = sepByCommaInd1 pExpr pos
            do! greater pos (skipString "]")

            return access
        }

    /// Parses an expression as a function call.
    let private pExprCall =
        parse {
            let! pos = getPosition
            do! any pos (skipChar '[') <?> "implicit function call"

            let! arguments = sepByCommaInd pArg pos
            do! greater pos (skipChar ']')

            return arguments
        }

    let private pImplicitMultiplication =
        parse {
            let! pos = getPosition
            let! num = exact pos pNumber |>> fun (lit, loc) -> ExprLiteral lit, loc
            let! var = greater pos pExprName

            return infixMapping "*" pos num var
        }

    type private WithPrefixExpr =
        | ExprCall of CosynArg list
        | TableAccess of CosynExpr list

    /// Parse array access or expr as function call.
    let private pWithPrefixExpr =
        choice [ pTableAccess |>> TableAccess
                 pExprCall |>> ExprCall ]

    let private handleWithPrefixExpr exp xs =
        let hta lst acc loc = ExprTableAccess(acc, lst), loc

        let hec lst acc loc =
            (ExprExprCall({ expr = acc; arguments = lst }), loc)

        let rec inner acc = function
            | [] -> acc
            | (TableAccess lst, loc) :: rest -> inner (hta lst acc loc) rest
            | (ExprCall lst, loc) :: rest -> inner (hec lst acc loc) rest

        inner exp xs

    /// Parse an expression, also allows parsing an array access (as it is left-recursive).
    let rec public pExpr =
        parse {
            let! exp = opp.ExpressionParser

            (* We include here the parsing of array accesses and implicit function call
               because, as parsable expressions, they are ambiguous and left recursive *)

            match! many (pWithLoc pWithPrefixExpr) with
            | [] -> return exp
            | xs -> return handleWithPrefixExpr exp xs
        }

    /// Parse any expression between parenthesis.
    let private pParens =
        pWithLoc
        <| between (skipChar '(') (skipChar ')') pExpr

    /// Parse any expression between parenthesis as an expression.
    let private pExprParens =
        pParens
        |>> fun (expr, loc) -> ExprParens expr, loc

    /// Parse an optional argument name for a procedure argument.
    let private pOptArgName =
        parse {
            let! pos = getPosition
            let! argName = attempt (atLeast pos pIdentifier .>> doubleDot)
            return argName, pos
        }

    /// Parse an argument for a function call.
    let private pArg =
        parse {
            match! opt pOptArgName with
            | Some (argName, pos) ->
                let! argValue = greater pos pExpr

                return
                    { name = Some argName
                      value = argValue }

            | None ->
                let! argValue = pExpr
                return { name = None; value = argValue }
        }

    /// Parse a call to a procedure.
    let private pProcCall =
        parse {
            let! pos1 = getPosition
            let! name = atLeast pos1 pName

            do! greater pos1 (skipChar '[')
            let! pos = getPosition |>> adjustPosition -1
            let! arguments = sepByCommaInd pArg pos
            do! atLeast pos (skipChar ']')

            let! pos2 = getPosition
            let loc = pos1, pos2
            let call = { name = name; arguments = arguments }

            return call, loc
        }

    /// Parse a call to a procedure as an expression.
    let private pExprProcCall =
        pProcCall
        |>>> fun (call, loc) -> ExprProcCall call, loc

    /// Parse a list of expressions in braces.
    let private pVector =
        parse {
            let! pos = getPosition
            do! atLeast pos (skipChar '{')
            let! xs = sepByCommaInd pExpr pos
            do! atLeast pos (skipChar '}')
            return xs
        }

    /// Parse a vector.
    let private pExprVector =
        pVector |>>> fun (xs, loc) -> ExprVector xs, loc

    /// Parse a matrix.
    let private pExprMatrix =
        parse {
            let! pos = getPosition
            do! atLeast pos (skipChar '{')

            let! firstRaw = pVector
            let columnNumber = firstRaw.Length

            let raw =
                between (skipChar '{') (skipChar '}')
                <| sepByArray (atLeast pos pExpr) (attempt <| atLeast pos (skipChar ',')) columnNumber

            do! atLeast pos (skipChar ',') >>% ()
            let! raws = sepByCommaInd raw pos

            do! atLeast pos (skipChar '}')
            let! pos' = getPosition

            let xs = firstRaw :: raws
            let loc = pos, pos'

            return ExprMatrix xs, loc
        }

    /// Parse a '`-`' followed by an expression.
    let private pNegation = pWithLoc (skipChar '-' >>. pExpr)

    /// Parse the negation as an expression.
    let private pExprNegation =
        pNegation
        |>> fun (expr, loc) -> ExprNegation expr, loc

    /// Parse a lambda expression.
    let private pImplicitFunc =
        parse {
            let! pos = getPosition
            let! arguments = many1Till (atLeast pos pIdentifier) (attempt <| greater pos (skipString "->"))
            let! value = greater pos pExpr

            return
                ExprImplicitFunction
                    { arguments = arguments
                      ivalue = value }
        }

    /// Parse a lambda expression as an expression.
    let private pExprImplicitFunc =
        pImplicitFunc |>>> fun (ifn, loc) -> ifn, loc

    /// Parse a type name with optional types qualifiers.
    let private pRegionName =
        parse {
            let! pos = getPosition
            let! name = any pos pName

            let! withTypes = optAttempt (greater pos (between (skipChar '<') (skipChar '>') (sepByCommaInd1 pName pos)))

            return name, withTypes
        }
        |>>> fun (xs, loc) -> RegionName xs, loc

    /// Parse a type name with types qualifiers.
    let private pImplicitRegionNameWithTypes =
        parse {
            let! pos = getPosition
            let! name = any pos pName

            let! withTypes =
                greater pos (between (skipChar '<') (skipChar '>') (sepByCommaInd1 pName pos))
                |>> Some

            return name, withTypes
        }
        |>>> fun (xs, loc) -> ExprRegion(RegionName xs, loc), loc

    /// Open or closed interval.
    type private OpenOrClosed =
        | Open
        | Closed

    /// Parse a '[' or a ']' as an open or closed interval.
    let private pOpenOrClosed =
        choice [ skipChar '[' >>% Open
                 skipChar ']' >>% Closed ]

    /// Parse a region interval.
    let private pInterval =
        parse {
            let! pos = getPosition

            let! ooc1 = any pos pOpenOrClosed
            let! from = atLeast pos pExpr

            do! atLeast pos (skipChar ',')

            let! upto = atLeast pos pExpr
            let! ooc2 = atLeast pos pOpenOrClosed

            let openLeft, openRight =
                match ooc1, ooc2 with
                | Open, Open -> false, true
                | Open, Closed -> false, false
                | Closed, Closed -> true, false
                | Closed, Open -> true, true

            return
                { openLeft = openLeft
                  openRight = openRight
                  from = from
                  upto = upto }
        }

    /// Parse a region interval.
    let private pRegionInterval =
        pInterval
        |>>> fun (inter, loc) -> RegionInterval inter, loc

    /// Parse an interval by specifying to which subtype it belongs.
    let private pIntervalSubRegion =
        parse {
            let! pos = getPosition
            let! interval = pInterval
            do! greater pos (skipChar ':')
            let! subRegion = greater pos pName

            return RegionIntervalSubRegion(interval, subRegion)
        }

    /// Parse an interval by specifying to which subtype it belongs as a region.
    let private pRegionIntervalSubRegion =
        pIntervalSubRegion
        |>>> fun (region, loc) -> region, loc

    /// Parse a set that enumerate its values.
    let private pSetEnum =
        parse {
            let! pos = getPosition

            let! values =
                between (atLeast pos (skipChar '{' <?> "a type")) (atLeast pos (skipChar '}')) (sepByCommaInd pExpr pos)

            return values
        }

    /// Parse a set that enumerate its values as a region.
    let private pRegionSetEnum =
        pSetEnum
        |>>> fun (enum', loc) -> RegionSet(SetEnum enum'), loc

    /// Parse an expression as a value for a region set.
    let private pSetSimpleValue = pExpr |>> SimpleValue

    /// Parse a variable name that belongs to a set.
    let private pFromSubSet =
        parse {
            let! pos = getPosition
            let! var = any pos pIdentifier
            do! greater pos (skipChar ':')
            let! belongsIn = greater pos pName

            return FromSubSet(var, belongsIn)
        }

    /// Parse any predicate value.
    let private pSetPredicatValue =
        choiceL [ attempt pFromSubSet; pSetSimpleValue ] "variable of the predicat"

    /// Parse a set with a predicat of belonging.
    let private pSetPredicat =
        parse {
            let! pos = getPosition
            do! atLeast pos (skipChar '{')

            let! value = atLeast pos pSetPredicatValue
            do! atLeast pos (skipChar '|')

            let! predicat = sepByCommaInd pExpr pos
            do! atLeast pos (skipChar '}')

            return { value = value; preidcat = predicat }
        }

    /// Parse a set with a predicat of belonging as a region.
    let private pRegionSetPredicat =
        pSetPredicat
        |>>> fun (spd, loc) -> RegionSet(SetPredicat spd), loc

    /// Parse any set definition.
    let private pSet =
        choiceL
            [ attempt pRegionSetPredicat
              pRegionSetEnum ]
            "a set"

    /// Parse a region tuple.
    let private pRegionTuple' =
        parse {
            let! pos = getPosition
            do! any pos (skipChar '(')
            let! values = sepByCommaInd1 pRegion pos
            do! greater pos (skipChar ')')

            return values
        }

    /// Parse a region tuple.
    let private pRegionTuple =
        pRegionTuple'
        |>>> fun (rt, loc) -> RegionTuple rt, loc

    /// Parse an arrow type.
    let private pRegionArrow =
        parse {
            let! pos1 = getPosition
            let! arrowList = sepBy1 (atLeast pos1 pRegion') (attempt <| greater pos1 (skipString "->"))
            let! pos2 = getPosition

            let loc = pos1, pos2

            return
                arrowList
                |> List.reduce (fun t1 t2 -> (RegionArrow(t1, t2), loc))
        }

    /// Parse an arrow types between parenthesis.
    let private pRegionParens =
        parse {
            let! pos = getPosition
            return! between (exact pos (skipChar '(')) (greater pos (skipChar ')')) pRegionArrow
        }

    /// Parse any region except the arrow type.
    let private pRegion' =
        choiceL
            [ attempt pRegionName
              attempt pRegionIntervalSubRegion
              attempt pRegionInterval
              attempt pRegionParens
              pRegionTuple
              pSet ]
            "a region"

    /// Parse any region.
    let private pRegion =
        attempt pRegionArrow
        <|> (pRegion' .>> notFollowedBy pRegionArrow)

    /// Parse the infinity symbol (return an unit).
    let private pInfinity =
        pWithLoc (keyword "infinity" <|> skipChar '∞')

    /// Parse the infinity symbol as an expression.
    let private pExprInfinity =
        pInfinity |>> fun (_, loc) -> ExprInfinity, loc

    /// Parse the "last expression" symbol.
    let private pLastExpr = pWithLoc ((keyword "%") >>. opt pint32)

    /// Parse the "last expression" symbol as an expression.
    let private pExprLastExpr =
        pLastExpr
        |>> fun (num, loc) -> ExprLastExpr num, loc

    /// Parse the "elif" part of the "if then else" expression.
    let private pElif pos p =
        parse {
            do! any pos (keyword "elif")
            let! cond = greater pos pExpr
            do! atLeast pos (keyword "then")
            let! ifSuccess = greater pos p

            return { cond = cond; ifSuccess = ifSuccess }
        }

    /// Parse the "if then else" expression.
    let private pIfThenElse p isElseOpt =
        parse {
            let! pos = getPosition
            do! any pos (keyword "if")
            let! cond = greater pos pExpr

            do! atLeast pos (keyword "then")
            let! ifSuccess = greater pos p
            let! elifList = many <| attempt (pElif pos p)

            let result =
                { cond = cond
                  ifSuccess = ifSuccess
                  elifList = elifList
                  ifFail = None }

            if not isElseOpt then

                do! atLeast pos (keyword "else")
                let! ifFail = greater pos p
                return { result with ifFail = Some ifFail }

            else

                match! optAttempt (atLeast pos (keyword "else")) with
                | None -> return result
                | Some _ ->
                    let! ifFail = greater pos p
                    return { result with ifFail = Some ifFail }
        }

    /// Parse a tuple.
    let private pTuple' p =
        parse {
            let! pos = getPosition
            do! any pos (skipChar '(')
            let! values = sepByCommaInd p pos
            do! greater pos (skipChar ')')

            return values
        }

    /// Parse an empty tuple.
    let private pEmptyTuple' _ =
        parse {
            let! pos = getPosition
            do! any pos (skipChar '(')
            do! greater pos (skipChar ')')

            return []
        }

    /// Parse any tuple.
    let private pTuple p = choice [ pTuple' p; pEmptyTuple' p ]

    /// Parse a literal as a pattern.
    let private pLitPattern =
        pLiteral
        |>> fun (lit, loc) -> PatternLiteral lit, loc

    /// Parse a tuple as a pattern.
    let private pTuplePattern =
        pTuple (pExpr |>> Pattern <|> (skipString "..." >>% Dots))
        |>>> fun (tpl, loc) -> PatternTuple tpl, loc

    /// Parse a call as a pattern.
    let private pCallPattern =
        pProcCall
        |>> fun (call, loc) -> PatternCall(call, loc), loc

    /// Parse a name as a pattern.
    let private pNamePattern =
        pName
        |>>> fun (name, loc) -> PatternName name, loc

    /// Parse any acceptable pattern.
    let private pPattern =
        choiceL
            [ pLitPattern
              pTuplePattern
              attempt pCallPattern
              pNamePattern ]
            "valid pattern"

    /// Parse the 'when' case pattern.
    let private pWhen =
        parse {
            let! pos = getPosition
            do! atLeast pos (keyword "when")

            (* We expect a 'term' and not an 'expression' because FParsec fails to resolve some
               ambiguities related to the `-` infix which conflicts with the `->` arrow, however
               this only limits us syntactically as a term as an expression in brackets, e.g. `(x > 0)`,
               works well. Hopefully this limitation is temporary... *)

            return! greater pos term
        }

    /// Parse the simple case for a pattern matching.
    let private pSimpleCase p =
        parse {
            let! pos = getPosition
            let! pattern = any pos pPattern

            let! when' = optAttempt pWhen

            do! greater pos (skipString "->")
            let! ifSuccess = greater pos p

            return SimpleCase(pattern, when', ifSuccess)
        }

    /// Parse the wildcard '_' as a case pattern.
    let private pWildcardCase p =
        parse {
            let! pos = getPosition
            do! any pos (skipChar '_')

            let! when' = optAttempt pWhen

            do! greater pos (skipString "->")
            let! ifSuccess = greater pos p

            return WildcardCase(when', ifSuccess)
        }

    /// Each type of cases in a pattern selection.
    let private pCase p =
        choice [ pSimpleCase p
                 pWildcardCase p ]

    /// Pattern matching parsing.
    let private pSelect p =
        parse {
            let! pos = getPosition
            do! any pos (keyword "select")
            let! toSelect = optAttempt <| greater pos pExpr
            let! cases = greater pos <| blockOf (pCase p)

            return { toSelect = toSelect; cases = cases }
        }

    /// Parse the "if then else" expression as an expression.
    let private pExprIfThenElse =
        pIfThenElse pExpr false
        |>>> fun (expr, loc) -> ExprIfThenElse expr, loc

    /// Parse the pattern matching statement.
    let private pExprSelect =
        pSelect pExpr
        |>>> fun (expr, loc) -> ExprSelect(expr, loc), loc

    let private pCosyinImplementObject =
        parse {
            let! pos = getPosition
            let! object = any pos pName

            let! arguments =
                optAttempt (atLeast pos (between (skipChar '<') (skipChar '>') (sepByCommaInd1 pRegion pos)))

            do! atLeast pos (keyword "with")

            let! impl =
                greater
                    pos
                    (blockOf (
                        choice [ attempt (pTopLEquationalProcedure true)
                                 pTopLProcedure true
                                 attempt pTopLConstDef
                                 pTopLFuncDef ]
                    ))

            return
                { object = object
                  arguments = arguments
                  impl = impl }
        }
        |>>> fun (expr, loc) -> ExprImplementObject(expr, loc), loc

    /// Parse a region as an expression.
    let private pExprRegion =
        parse {
            let! pos = getPosition
            do! any pos (keyword "region")
            let! region = greater pos pRegion
            return ExprRegion region
        }
        |>>> fun (reg, loc) -> reg, loc

    /// Parse any tuple as an expression.
    let private pExprTuple =
        pTuple pExpr
        |>>> fun (xs, loc) -> ExprTuple xs, loc

    let private pTypeHole = pWithLoc (skipChar '?' >>. pIdentifier)

    /// Parse a type hole.
    let private pExprTypeHole =
        pTypeHole
        |>> fun (hole, loc) -> ExprTypeHole hole, loc

    /// Parse the the colon syntax, `initial : increment : terminator`.
    let private pInitIncTerm =
        parse {
            do! skipChar '{'
            let! pos = getPosition |>> adjustPosition -1

            let! initial = greater pos pExpr .>> atLeast pos (skipChar ':')
            let! increment = optAttempt (greater pos pExpr .>> atLeast pos (skipChar ':'))
            let! terminator = greater pos pExpr

            do! atLeast pos (skipChar '}')
            return initial, increment, terminator
        }

    /// Parse the the colon syntax, `initial : increment : terminator` as expression.
    let private pExprInitIncTerm =
        pInitIncTerm
        |>>> fun (iit, loc) -> ExprInitIncTerm iit, loc

    /// Parse a list/vector comprehension of the form `{ value for x, ..., z in src }`.
    let private pListComprehension =
        parse {
            let! pos = getPosition
            do! any pos (skipChar '{')

            let! value = greater pos pExpr
            do! greater pos (keyword "for")

            let! variables = sepByCommaInd1 pIdentifier pos
            do! greater pos (keyword "in")

            let! src = greater pos pExpr
            do! atLeast pos (skipChar '}')

            return value, variables, src
        }

    /// Parse a list/vector comprehension as an expression.
    let private pExprListComprehension =
        pListComprehension
        |>>> fun (lc, loc) -> ExprListComprehension lc, loc

    /// Parse tensor index up and down.
    let private pUpDown =

        let pbtw =
            choice [ between (skipChar '{') (skipChar '}') (sepBy1 pIdentifier' spaces1)
                     pIdentifier' |>> fun a -> [ a ] ]

        choice [ skipChar '^' >>. pbtw |>> List.map TUp
                 skipChar '_' >>. pbtw |>> List.map TDown ]

    /// Parse the tensor indices notation.
    let private pTensorIndexNotation =
        pWithLoc (
            pipe2 pIdentifier (many1 pUpDown) (fun id xs -> { tname = id; indices = List.concat xs })
            |>>> ExprTensorIndexNotation
        )

    /// A term is a single expression without operator.
    let private term =

        let rawTerm =
            choiceL
                [ attempt pImplicitMultiplication
                  pExprLiteral
                  attempt pCosyinImplementObject
                  pExprTypeHole
                  attempt pExprImplicitFunc
                  attempt pExprListComprehension
                  pExprInfinity
                  pExprLastExpr
                  pExprRegion
                  pExprIfThenElse
                  pExprSelect
                  attempt pTensorIndexNotation
                  attempt pExprProcCall
                  attempt pImplicitRegionNameWithTypes
                  pExprName
                  attempt pExprParens
                  pExprTuple
                  attempt pExprMatrix
                  attempt pExprVector
                  pExprInitIncTerm ]
                "a valid term"

        /// Parse a number with a unicode superscript integer exponent.
        let pWithUEXP =
            tuple2 rawTerm pUExp
            |>>> fun (ep, loc) -> ExprWithUnicodeExponent ep, loc

        choice [ attempt pWithUEXP; rawTerm ]

    // Terms are added to the expression parser.
    do opp.TermParser <- term .>> whitespaces


    (* Parsing of top level definitions. *)


    /// Parse a comment at the top level and ignore the content.
    let private pTopLComment =
        parse {
            let! pos = getPosition
            return! any pos <| lineComment "#" >>% TopLComment
        }

    /// Parse function definition.
    let private pTopLFuncDef =
        parse {
            let! pos1 = getPosition
            let! name = pIdentifier

            let! parameters = betweenHooks (sepByCommaInd pIdentifier pos1)
            do! whitespaces >>. skipString ":=" >>% ()

            let! value = greater pos1 pExpr
            let! pos2 = getPosition

            let loc = pos1, pos2

            return
                TopLFuncDef(
                    { name = name
                      parameters = parameters
                      withConstraint = []
                      value = value },
                    loc
                )
        }

    /// Parse constant definition.
    let private pTopLConstDef =
        parse {
            let! pos = getPosition
            let! name = sepByCommaInd1 pIdentifier pos
            do! greater pos (skipString ":=")
            let! value = greater pos pExpr

            return { name = name; constValue = value }
        }
        |>>> TopLConstDef

    /// Parse the "perform" statement.
    let private pTopLPerform =
        parse {
            let! pos = getPosition
            do! any pos (keyword "perform")
            let! expr = greater pos pExpr
            return TopLPerform expr
        }

    /// Parse the "do" statement.
    let private pTopLDo =
        parse {
            let! pos = getPosition
            do! any pos (keyword "do")
            let! expr = greater pos pExpr
            return TopLDo expr
        }

    /// Parse a variable setting definition.
    let private pTopLSettingVar =
        parse {
            let! pos = getPosition
            do! any pos (keyword "set")
            let! names = greater pos (sepByCommaInd1 pIdentifier pos)
            do! greater pos (skipChar ':')
            let! region = greater pos pRegion

            return { names = names; type' = region }
        }
        |>>> TopLSetVar

    /// Parse the "return" statement.
    let private pTopLReturn =
        parse {
            let! pos = getPosition
            do! any pos (keyword "return")
            let! value = greater pos pExpr

            return TopLReturn value
        }

    /// Parse a non-constant definition.
    let private pTopLMutableVar =
        parse {
            let! pos = getPosition
            do! any pos (keyword "mutable")
            let! id = greater pos pIdentifier

            let! region = optAttempt (greater pos (skipChar ':') >>. greater pos pRegion)

            do! greater pos (skipString ":=")
            let! value = greater pos pExpr

            return
                { name = id
                  type' = region
                  value = value }
        }
        |>>> TopLMutableVar

    /// Changes the value of a non-constant construction.
    let private pTopLUpateVar =
        parse {
            let! pos = getPosition
            let! var = any pos (attempt pExprName <|> pExpr)    // Dont work...  Ex.:  table.[0] <- 1  is parsed as the inequality  (table.[0] < ...)
            do! greater pos (skipString "<-")
            let! value = greater pos pExpr

            return TopLUpdateVar(var, value)
        }

    /// Parse the pattern matching statement.
    let private pTopLSelect =
        parse { return! pSelect pBody |>>> TopLSelect }

    /// Parse the "if then else" expression as a top level structure.
    let private pTopLIfThenElse =
        parse {
            let! pos = getPosition

            let! ifte = any pos <| pIfThenElse pBody true

            return TopLIfThenElse ifte
        }

    /// Parse a loop of the form `for x in xs`.
    let private pTopLForLoop =
        parse {
            let! pos = getPosition
            do! any pos (keyword "for")

            let! loopVariables = sepByCommaInd1 pIdentifier pos
            do! atLeast pos (keyword "in")

            let! inRanges = sepByCommaInd1 pExpr pos
            do! skipNewline
            let! body = greater pos pBody

            let! pos' = getPosition
            let loc = pos, pos'

            return
                TopLForLoop(
                    { loopVariables = loopVariables
                      inRanges = inRanges
                      body = body },
                    loc
                )
        }

    /// Parse a loop of the form `while <condition>`
    let private pTopLWhileLoop =
        parse {
            let! pos = getPosition
            do! any pos (keyword "while")
            let! whileCondition = greater pos pExpr

            do! skipNewline
            let! body = greater pos pBody

            let! pos' = getPosition
            let loc = pos, pos'

            return
                TopLWhileLoop(
                    { loopCondition = whileCondition
                      body = body },
                    loc
                )
        }

    /// Parse `breakloop` as a loop breaking statement.
    let private pTopLBreak = keyword "breakloop" >>% TopLBreakLoop

    /// Parse a loop of the form `do <body> while <condition>`
    let private pTopLDoWhileLoop =
        parse {
            let! pos = getPosition
            do! any pos (keyword "do")

            let! body = greater pos pBody
            do! exact pos (keyword "while")
            let! whileCondition = greater pos pExpr

            let! pos' = getPosition
            let loc = pos, pos'

            return
                TopLDoWhileLoop(
                    { loopCondition = whileCondition
                      body = body },
                    loc
                )
        }

    /// Parse the 'latex' statement.
    let private pTopAddLatex =
        parse {
            let! pos = getPosition
            do! any pos (keyword "latex")
            let! exp = greater pos pExpr
            do! atLeast pos (keyword "is")

            let! latex =
                greater
                    pos
                    (pWithLoc
                     <| between (skipChar ''') (skipChar ''') (manySatisfy ((<>) ''')))

            return TopLAddLatex(exp, latex)
        }

    (* Not all toplevel constructs are usable in procedures and vis-versa, e.g. the `return`
       statement makes no sense outside a procedure, just as `namespace` makes no sense in a procedure. *)

    /// the different constructions accepted in the body of a procedure.
    let private pAcceptableTopLevelWithinBody =
        choiceL
            [ pTopLPerform
              attempt pTopLDo
              pTopAddLatex
              pTopLReturn
              pTopLSelect
              pTopLIfThenElse
              pTopLForLoop
              pTopLWhileLoop
              pTopLBreak
              pTopLDoWhileLoop
              pTopLMutableVar
              attempt pTopLUpateVar
              attempt pTopLConstDef
              pTopLFuncDef
              pTopLSettingVar
              pTopLComment ]
            "statement"

    /// Parse the content of procedure.
    let private pBody =
        between
            spaces
            spaces
            (blockOf pAcceptableTopLevelWithinBody
             <?> "a block of statements")

    /// Parse an expression as a default value.
    let private pDefaultValueExpr =
        pExpr
        |>>> fun (expr, loc) -> DefaultValueExpression expr, loc

    /// Parse the "current variable" default value.
    let private pDefaultValueCurrentVar =
        keyword "CurrentVariable"
        |>>> fun (_, loc) -> DefaultValueCurrentVar, loc

    /// Parse any default value.
    let private pDefaultValue =
        choiceL
            [ attempt pDefaultValueCurrentVar
              pDefaultValueExpr ]
            "a default value (an expression)"

    /// Parse a parameter of a procedure.
    let private pProcParam =
        parse {
            let! pos = getPosition
            let! isMutable = any pos (keyword "mutable") >>% true <|>% false

            let indent =
                match isMutable with
                | true -> greater
                | false -> any

            let! name = indent pos (pIdentifier <?> "a parameter name")
            do! greater pos (skipChar ':' <?> "a type annotation")
            let! type' = greater pos pRegion

            let! defaultValue =
                optAttempt (
                    greater pos (keyword "or")
                    >>. greater pos pDefaultValue
                )

            return
                { name = name
                  type' = type'
                  isMutable = isMutable
                  defaultValue = defaultValue }
        }

        |>>> fun (par, loc) -> par, loc

    let private pCtorOrProc asCtor =
        keyword <| if asCtor then "constructor" else "procedure"

    /// Parse a procedure definition.
    let private pTopLProcedure (asCtor: bool) =
        parse {
            let! pos = getPosition
            do! any pos (pCtorOrProc asCtor)
            let! name = greater pos (pIdentifier <?> "a procedure name")

            let! parameters = greater pos <| betweenHooks (sepByCommaInd pProcParam pos)
            let! rtype = optAttempt (greater pos (skipChar ':') >>. greater pos pRegion)

            let! body = greater pos pBody

            return
                { name = name
                  parameters = parameters
                  returnType = rtype
                  body = body }
        }

        |>>> TopLProcedure

    /// Parse a procedure definition pattern by explicit selection.
    let private pEqProcCase pos =
        let pBody =
            choice [ // It allows parsing of a simple expression, so you don't have to write heavy
                     // stuff like `return x` when the syntax already lends itself to that, pretty much.
                     attempt pBody
                     pExpr |>> fun a -> [ TopLReturn a ] ]

        tuple3
            pProcCall
            (optAttempt (greater pos pWhen))
            (greater pos (skipString "->")
             >>. greater pos pBody)

    /// Parse a procedure by explicit selection, it is "equational pattern matching".
    let private pTopLEquationalProcedure (asCtor: bool) =
        parse {
            let! pos = getPosition
            do! any pos (pCtorOrProc asCtor)
            let! cases = greater pos <| blockOf (pEqProcCase pos)

            let name =
                let (a, _), _, _ = cases.Head
                a.name

            if cases.All(fun (({ name = name' }, _), _, _) -> compareNames name name') then
                return TopLEquationalProcedure { name = name; cases = cases }
            else
                return!
                    failf
                        "A procedure defined by an equational style expects the same procedure name (%A) for each case"
                        name
        }

    /// Parse a file or directory path.
    let private pURL =
        let nchar = satisfy (fun c -> c <> ''')

        pWithLoc
        <| between (skipChar ''') (skipChar ''') (manyChars nchar)
        <?> "path/url"

    /// Parse the addition of a new library to use.
    let private pTopLUse =
        let useExternal pos =
            parse {
                do! greater pos (keyword "extern")
                let! url = greater pos pURL
                return TopLUseExternalLib url
            }

        let useInternal pos =
            parse {
                let! libName = greater pos pName
                return TopLUseInternalLib libName
            }

        parse {
            let! pos = getPosition
            do! any pos (keyword "use")
            return! choice [ attempt (useInternal pos); useExternal pos ]
        }

    /// Parse a "preprocessor" directive.
    let private pDirective =

        let directive =
            choice [ keyword "debug" >>% DirectiveDebug
                     keyword "script" >>% DirectiveScript ]

        parse {
            let! pos = getPosition
            do! any pos (skipChar '%') <?> "a directive"
            return! greater pos directive |>> TopLDirective
        }

    (* Units of measures. *)

    /// Unit-related arithmetic is handled by its own precedence parser.
    let private unitArithOpp =
        new OperatorPrecedenceParser<UnitArith, unit, unit IndentState>()

    /// Any valid unit arithmetic.
    let private unitArith = unitArithOpp.ExpressionParser

    /// Constant real factor.
    let private pUnitArithConstantNumber =
        choice [ pfloat |>> UnitArithConstFloat
                 pint32 |>> UnitArithConstInteger ]

    /// A unit can be a combination of other units.
    let private pUnitArithConstWithOptUnit =
        parse {
            let! pos = getPosition
            let! factor = any pos pUnitArithConstantNumber

            match! optAttempt (greater pos pIdentifier) with
            | Some (symbol, pos) ->
                match unitList.TryFind symbol with
                | Some u -> return UnitArithConstant(UnitArithConstWithUnit(factor, u))
                | None -> return! failf "no units were found for the symbol [lightskyblue3_1]%s[/]" symbol
            | None -> return UnitArithConstant factor
        }

    /// Using a non-SI unit.
    let private pNonSIUnit =
        parse {
            let! pos = getPosition
            do! any pos (keyword "nonSI")
            let! id = greater pos pString'
            return id
        }

    /// Liyh follows the conventions of the International System and defines each unit as a linear
    /// combination of the SI basic dimensions.
    let private pBasicDimension =
        choiceL
            [ keyword "Time" >>% DTime
              keyword "Length" >>% DLength
              keyword "Mass" >>% DMass
              keyword "ElectricCurrent" >>% DElectricCurrent
              keyword "Current" >>% DElectricCurrent
              keyword "Temperature" >>% DTemperature
              keyword "AbsoluteTemperature" >>% DTemperature
              keyword "AmountOfSubstance" >>% DAmountOfSubstance
              keyword "Amount" >>% DAmountOfSubstance
              keyword "LuminousIntensity" >>% DLuminousIntensity
              pNonSIUnit |>> DNonSI ]
            "a SI fundamental dimension"

    unitArithOpp.TermParser <-
        choiceL
            [ pUnitArithConstWithOptUnit
              pBasicDimension |>> UnitArithBasicDimension
              between (skipChar '(' >>. spaces) (skipChar ')' >>. spaces) unitArith ]
            "the definition of a unit in terms of a linear combination of other units"
        .>> spaces

    (* Only multiplicative relationships exist between the units. *)

    do unitArithOpp.AddOperator(InfixOperator("*", spaces, 2, Associativity.Left, curry UnitArithMultiplication))
    do unitArithOpp.AddOperator(InfixOperator("/", spaces, 2, Associativity.Left, curry UnitArithDivision))
    do unitArithOpp.AddOperator(InfixOperator("**", spaces, 3, Associativity.Left, curry UnitArithPower))

    //let private pUnproportionalUnit =
    //    let pUnitSymbol =
    //        unitList.GetUnitList.Select(fun { symbol = s } -> s)
    //        |> Seq.toArray
    //        |> Array.map pstring
    //
    //    pipe3 (spaces >>. choice pUnitSymbol) (spaces >>. skipChar '+') (spaces >>. pfloat) (fun u _ k ->
    //        ((unitList.tryFind u).Value, k)
    //        |> UnitArithUnproportional)

    /// Parsing and adding a new unit of measure.
    let private pTopLAddUnit =
        parse {
            let! pos = getPosition
            do! any pos (keyword "unit")
            let! unitName, _ = greater pos pIdentifier

            if Array.contains (unitName.ToLower()) basicDimensions then
                return! failf "a unit cannot be named after a dimension ([lightskyblue3_1]%s[/] here)" unitName
            else

                do! greater pos (skipChar ',')
                let! unitSymbol, _ = greater pos pIdentifier

                do! greater pos (keyword "is")
                let! dim = greater pos unitArith

                do addPostfixOp unitSymbol UnitPrecedence false (postfixMapping unitSymbol)

                do
                    unitList.AddUnit
                        { name = unitName
                          symbol = unitSymbol
                          unit = dim }

                return TopLAddUnit
        }

    type private NewOperator =
        | NewOpInfix of OpName * OpName * OpName
        | NewOpPostfix of OpName * OpName
        | NewOpPrefix of OpName * OpName

        member this.getOpStr =
            match this with
            | NewOpInfix ((opStr, _), _, _)
            | NewOpPostfix ((opStr, _), _)
            | NewOpPrefix ((opStr, _), _) -> opStr

    let private reservedOperators =
        [ ":="
          "..."
          "."
          "?"
          "|||"
          ","
          ":"
          "<-"
          "->" ]

    let rec private mapChrStr (fn: char -> string) (xs: string) : string = [| for x in xs -> fn x |].ToString()

    /// Parse a valid operator name.
    let private pOpStr =

        let symbols =
            @"+-*/.%>=<&|~,@$:;!?"
            + "abcdefghijklmnopqrstuvwxyz"
            + "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

        let errmsg =
            "a valid combination of "
            + mapChrStr (sprintf "[lightskyblue3_1]%c[/], ") symbols

        pWithLoc (
            many1 (anyOf symbols) <?> errmsg
            |>> System.String.Concat
        )
        >>= function
            | op, _ when List.contains op reservedOperators ->
                failf "The operator [lightskyblue3_1]%s[/] is reserved" op

            | op, _ when List.contains op reservedKeywords -> failf "The keyword [lightskyblue3_1]%s[/] is reserved" op

            | op, loc -> preturn (op, loc)

    /// Parse the case-insensitive `priorityOf` pseudo-procedure.
    /// This parser fails if the given operator does not exist.
    let private pPriorOf =
        parse {
            let! pos = getPosition
            do! any pos (keyword "priorityOf")
            let! (opStr, _) = greater pos (betweenHooks (whitespaces >>. pOpStr))
            return operatorList.tryGetPrior opStr, opStr
        }

        >>= function
            | None, opStr -> failf "the operator '%s' doesn't exist" opStr
            | Some prior, _ -> preturn prior

    (* Parsing the definition patterns of new operators. *)

    let private pAddInfixNotation pos =
        parse {
            let! id1 = greater pos pIdentifier
            let! opStr = greater pos pOpStr
            let! id2 = greater pos pIdentifier
            return NewOpInfix(opStr, id1, id2)
        }

    let private pAddPostfixNotation pos =
        parse {
            let! id = greater pos pIdentifier
            let! opStr = greater pos pOpStr
            return NewOpPostfix(opStr, id)
        }

    let private pAddPrefixNotation pos =
        parse {
            let! opStr = greater pos pOpStr
            let! id = greater pos pIdentifier
            return NewOpPrefix(opStr, id)
        }

    let private pNewOp pos =
        choiceL
            [ attempt <| pAddInfixNotation pos
              attempt <| pAddPostfixNotation pos
              pAddPrefixNotation pos ]
            "valid notation"

    /// Parse the associativity parameter of the new operators.
    let private pAssoc pos asOption =
        parse {
            do!
                greater pos (keyword "associativity")
                >>. doubleDot

            let pAssocValue =
                match asOption with
                | true ->
                    [ keyword "true" >>% Associativity.Left
                      keyword "false" >>% Associativity.None ]

                | false ->
                    [ keyword "left" >>% Associativity.Left
                      keyword "right" >>% Associativity.Right
                      keyword "none" >>% Associativity.None ]

                |> choice

            return! greater pos pAssocValue
        }

    /// Parse the priority parameter of the new operators.
    let private pPrior pos =
        tuple2
            (greater pos (keyword "priority")
             >>. whitespaces
             >>. skipChar ':')
            (greater pos <| choice [ attempt pPriorOf; pint32 ])

        >>= function
            | (_, prior) when prior <= 0 -> fail "the priority of an operation must be strictly greater than 0"
            | (_, prior) -> preturn prior

    /// Parse associativity first, then priority.
    let private pAssocAndPrior asOption =
        parse {
            let! pos = getPosition
            let! assoc = pAssoc pos asOption
            do! skipNewline
            let! prior = pPrior pos

            return assoc, prior
        }

    /// Parse priority first, then associativity.
    let private pPriorAndAssoc asOption =
        parse {
            let! pos = getPosition
            let! prior = pPrior pos
            do! skipNewline
            let! assoc = pAssoc pos asOption

            return assoc, prior
        }

    /// Utility to add to the operator table and the precedence parser table a new operator.
    let private addNewNotation assoc prior (referTo: CosynExpr) =
        function
        | (NewOpInfix ((opStr, _), (l, _), (r, _))) ->
            let prop =
                { leftSide = l
                  rightSide = r
                  referTo = new List<_>([ referTo ])
                  assoc = assoc
                  prior = prior }

            operatorList.addLiyhInfixOp opStr prop
            addInfixOp opStr prior assoc (infixMapping opStr)

        | (NewOpPostfix ((opStr, _), (ex, _))) ->
            let prop =
                { leftSide = ex
                  referTo = new List<_>([ referTo ])
                  assoc = fpAssocToOptAssoc assoc
                  prior = prior }

            operatorList.addLiyhPostfixOp opStr prop
            addPostfixOp opStr prior (fpAssocToOptAssoc assoc) (postfixMapping opStr)

        | (NewOpPrefix ((opStr, _), (ex, _))) ->
            let prop =
                { rightSide = ex
                  referTo = new List<_>([ referTo ])
                  assoc = fpAssocToOptAssoc assoc
                  prior = prior }

            operatorList.addLiyhPrefixOp opStr prop
            addPrefixOp opStr prior (fpAssocToOptAssoc assoc) (postfixMapping opStr)

    /// Adds a new notation whose operator already exists.
    let private addNewOverrideNotation referTo =
        function
        | NewOpInfix ((opStr, _), _, _) -> operatorList.addLiyhInfixOpOverride opStr referTo
        | NewOpPostfix ((opStr, _), _) -> operatorList.addLiyhPostfixOpOverride opStr referTo
        | NewOpPrefix ((opStr, _), _) -> operatorList.addLiyhPrefixOpOverride opStr referTo

    let [<Literal>] private IsOverride = true
    let [<Literal>] private IsNotOverride = false

    /// Parse a new notation addition and add the new notation to the tables.
    let private pTopLAddNotation =
        let pNotationIs =
            parse {
                let! pos = getPosition
                do! any pos (keyword "notation")
                let! newOp = pNewOp pos

                do! greater pos (keyword "is")
                let! referTo = greater pos pExpr

                return (newOp, referTo), (operatorList.tryFind newOp.getOpStr).IsSome
            }

        let pNotationProps newOp referTo pos =
            parse {
                do! skipNewline
                do! atLeast pos (keyword "with") .>> whitespaces
                do! opt skipNewline >>% ()

                let asOption =
                    match newOp with
                    | NewOpInfix _ -> false
                    | _ -> true

                let! (assoc, prior) =
                    attempt (pPriorAndAssoc asOption)
                    <|> pAssocAndPrior asOption

                do addNewNotation assoc prior referTo newOp

                return ()
            }

        parse {
            match! getPosition .>>. pNotationIs with
            | pos, ((newOp, referTo), IsNotOverride) ->
                do! pNotationProps newOp referTo pos
                return TopLAddNotation

            | _, ((newOp, referTo), IsOverride) ->

                // We need to run the following function, plus if it returns `false` then an
                // error has occurred, normally this shouldn't happen as we make sure to direct
                // the program so that the error in question doesn't happen, but we might as well
                // check to make sure it does with an assertion.
                assert addNewOverrideNotation referTo newOp

                return TopLAddNotation
        }

    /// Parse a new constructor.
    let private pCtor =
        parse {
            let! pos = getPosition
            let! name = any pos pIdentifier

            let! parameters =
                betweenHooks (sepByCommaInd pProcParam pos)
                <|>% []

            return SimpleCtor(name, parameters)
        }

    /// Parse an enumeration.
    let private pTopLEnumeration =
        parse {
            let! pos = getPosition
            do! any pos (keyword "enumeration")
            let! name = greater pos pIdentifier

            let! variableTypes =
                between (skipChar '<') (skipChar '>') (sepByCommaInd1 pIdentifier pos)
                |> optAttempt

            let! constructors = greater pos (blockOf pCtor)

            return
                TopLEnumDef
                    { name = name
                      variableTypes =
                        match variableTypes with
                        | None -> []
                        | Some xs -> xs
                      constructors = constructors }
        }

    /// Parse a record.
    let private pTopLRecordDef =
        parse {
            let! pos = getPosition
            do! any pos (keyword "record")
            let! name = greater pos pIdentifier

            let! variableTypes =
                between (skipChar '<') (skipChar '>') (sepByCommaInd1 pIdentifier pos)
                |> optAttempt

            let! fields = greater pos (blockOf pProcParam)

            return
                TopLRecordDef
                    { name = name
                      variableTypes =
                        match variableTypes with
                        | None -> []
                        | Some xs -> xs
                      fields = fields }
        }

    /// Parse the alias statement.
    let private pTopLAlias =
        parse {
            let! pos = getPosition

            do! any pos (keyword "alias")
            let! id1 = greater pos pIdentifier

            do! greater pos (keyword "is")
            let! id2 = greater pos pIdentifier

            return TopLAlias(id1, id2)
        }

    /// Parse a system of equations.
    let private pTopLSystem =
        parse {
            let! pos = getPosition
            do! any pos (keyword "system")
            let! name = greater pos pIdentifier

            (* Any expression is accepted because, for example, a definition of `f[x]` can define
               an equation and be used in the system as an equation. *)

            let! equations = greater pos (blockOf pExpr) .>> spaces
            return TopLSystem(name, equations)
        }

    let private pObjectParameterTypeVar = pIdentifier |>> TypeVar

    let private pObjectParameterSpecificTypeVar =
        parse {
            let! pos = getPosition
            let! id = any pos pIdentifier
            do! greater pos (skipChar ':')
            let! ty = greater pos pRegion
            return SpecificTypeVar(id, ty)
        }

    let private pObjectParameter =
        choice [ attempt pObjectParameterSpecificTypeVar
                 pObjectParameterTypeVar ]

    let private pObjectProperties =
        parse {
            let! pos = getPosition
            let! id = any pos pIdentifier
            do! greater pos (skipChar ':')
            let! ty = greater pos pRegion
            return (id, ty)
        }

    let private pCosynObject =
        parse {
            let! pos = getPosition
            do! any pos (keyword "object")

            let! name = greater pos pName

            let! parameters =
                optAttempt
                <| between (skipChar '<') (skipChar '>') (greater pos (sepByCommaInd1 pObjectParameter pos))

            let! inherits = optAttempt (greater pos (keyword "is" >>. greater pos pRegion))
            let! properties = greater pos (blockOf pObjectProperties)

            return
                TopLObject
                    { name = name
                      parameters = parameters
                      inherits = inherits
                      properties = properties }
        }

    /// Parse a "description", this is a documentation comment.
    let private pDescription =
        many1 (skipString "|||" <?> "" >>. restOfLine true)
        |>> List.fold (fun acc s -> acc + s.Trim()) ""

    /// Parse a namespace definition.
    let private pTopLNamespace =
        parse {
            let! pos = getPosition
            do! any pos (keyword "namespace")

            let! extends =
                optAttempt <| greater pos (keyword "extends")
                |>> Option.isSome

            let! id = greater pos pName

            let! toExport =
                optAttempt
                <| greater pos (between (skipChar '(') (skipChar ')') (sepByCommaInd pIdentifier pos))

            let! body = greater pos <| blockOf pTopLevelInsideNamespace

            return TopLNamespace(id, extends, toExport, body)
        }

    /// Parse any top level definition and statement usable from the very first toplevel.
    let private pTopLevel' =
        choiceL
            [ pTopLPerform
              pCosynObject
              pTopLDo
              pTopAddLatex
              pTopLAddUnit
              pTopLAddNotation
              pTopLUse
              attempt (pTopLEquationalProcedure false)
              pTopLProcedure false
              pTopLEnumeration
              pTopLRecordDef
              pTopLAlias
              pTopLSystem
              pTopLNamespace
              attempt pTopLConstDef
              pTopLSettingVar
              pTopLFuncDef
              pTopLComment ]
            "valid definition or statement (if you want to enter an expression, use the [lightskyblue3_1]perform[/] keyword)"

        .>> spaces

    /// Parsing a description (a non-ignored comment) with a higher level statement.
    let private pTopLWithDescription topLvl =
        tuple2 pDescription topLvl |>> TopLWithDescription

    /// Parse any top level definition and statement.
    let private pTopLevel =
        choice [ pTopLWithDescription pTopLevel'
                 pTopLevel'
                 pDirective .>> spaces ]

    /// The toplevel inside a namespace.
    let private pTopLevelInsideNamespace' =
        choiceL
            [ pCosynObject
              pTopAddLatex
              pTopLAddUnit
              pTopLAddNotation
              pTopLUse
              attempt (pTopLEquationalProcedure false)
              pTopLProcedure false
              pTopLEnumeration
              pTopLRecordDef
              pTopLAlias
              pTopLSystem
              attempt pTopLConstDef
              pTopLSettingVar
              pTopLFuncDef
              pTopLComment ]
            "valid definition or statement"

        .>> spaces

    /// Parse any valid top level definition and statement inside a namespace.
    let private pTopLevelInsideNamespace =
        choice [ pTopLWithDescription pTopLevelInsideNamespace'
                 pTopLevelInsideNamespace' ]

    /// Parse a block of toplevel definition.
    let private pTopLevelBlock = blockOf pTopLevel

    /// Parse an entire program.
    let private pLiyhProgram =
        choice [ attempt pTopLevelBlock
                 spaces >>% [] ]
        .>> eof


    (* Make the parser run. *)


    let rec private getParsingMessage = function
        | Expected s when s <> "end of input" -> sprintf "expected %s" s
        | ExpectedStringCI s -> sprintf "expected the [lightskyblue3_1]%s[/] keyword" (correctMarkup s)
        | ExpectedString s -> sprintf "expected [lightskyblue3_1]%s[/]" (correctMarkup s)
        | NestedError (p, _, x) ->
            System.String.Join(", or ", Seq.map getParsingMessage (ErrorMessageList.ToSortedArray x))
        | Message s -> s
        | a -> ""

    // https://github.com/stephan-tolksdorf/fparsec/blob/fdd990ad5abe32fd65d926005b4c7bd71dd2384f/FParsec/Error.fs

    let rec private relevantPosition = function
        | NestedError (p, _, _) -> Some p
        | _ -> None

    let private resultLiyhParser (diag: FileDiagnostic) = function
        | Success (res, _, _) ->
            let res = List.filter (function TopLComment -> false | _ -> true) res

            if List.isEmpty res then
                diag.AddDiagnostic
                    { isInternal = false
                      kind = DiagnosticNote "Parsing"
                      relevantElement = None
                      location = None
                      streamName = diag.FilePath
                      messages = [ sprintf "The file [lightskyblue3_1]%s[/] does not contain any code." diag.FilePath.Value ]
                      importance = Unhelpful
                      code = None }

            Some res

        | Failure (msg, err, _) ->

            // printfn "%A" msg

            let withErrorMessageList action =
                Seq.map action (ErrorMessageList.ToSortedArray err.Messages)

            let pos =
                match Seq.last (withErrorMessageList relevantPosition) with
                | None -> err.Position
                | Some p -> p

            let messages =
                getParsingMessage
                |> withErrorMessageList
                |> Seq.filter ((<>) "")
                |> Seq.map (fun s ->
                    (string (System.Char.ToUpper s.[0])
                     + s.[1..s.Length - 1])
                     + ".")
                |> Seq.toList

            diag.AddDiagnostic
                { isInternal = false
                  kind = DiagnosticError "Parsing"
                  relevantElement = None
                  location = Some(pos, pos)
                  streamName = diag.FilePath
                  messages = messages
                  importance = Major
                  code = None }

            None

    /// Launch the parser on the given text.
    let public startParser (diag: FileDiagnostic) =
        runParser pLiyhProgram () diag.FileContent
        |> resultLiyhParser diag

    /// Launch the parser on the given file.
    let public startParserOnFile path (diag: FileDiagnostic) =
        match diag.FilePath with
        | Some _ -> runParser pLiyhProgram () diag.FileContent
        | None -> Indentation.runParserOnFile pLiyhProgram () path
        |> resultLiyhParser diag

    /// Launch the expression parser on the given text.
    let public startExprParser = runParser pExpr ()

    /// Retrieves all units of measurement that have been defined.
    let public getUnits () = unitList

    /// Retrieves all operators that have been defined.
    let public getOperators () = operatorList
