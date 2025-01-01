namespace Liyh.Language.Evaluation

(*
 *
 *  For debugging purposes, we provide an intermediate language parser ("LiyhIL" if you like) in order
 *  to run in the VM directly the "bytecode" entered in a text file or a string. Since in fact this module
 *  is of no use to Liyh, the code has been written with little care and without performance optimisation.
 *
 *)

module ILParser =
    open System.Collections.Generic
    open Liyh.Kernel
    open Liyh.Language.Evaluation.IL
    open FParsec

    type private ILValue =
        | Integer of int
        | Label of string
        | Data of string
        | Register of int
        | String of string
        | Symbol of ISymbolic

    let private ws = many (pchar ' ' <|> pchar '\t')
    let private ws1 = many1 (pchar ' ' <|> pchar '\t')

    let private pComment = skipChar ';' >>? skipRestOfLine true <?> ""

    /// Parse valid identifier.
    let private pIdentifier =
        let isAsciiIdStart = (fun c -> isAsciiLetter c || c = '_')

        let isAsciiIdContinue c =
            isDigit c || c = ''' || isAsciiIdStart c

        identifier (
            IdentifierOptions(
                isAsciiIdStart = isAsciiIdStart,
                isAsciiIdContinue = isAsciiIdContinue,
                normalization = System.Text.NormalizationForm.FormKD,
                normalizeBeforeValidation = true,
                allowAllNonAsciiCharsInPreCheck = true)
        ) >>= preturn

    let private pString' =
        let unescape =
            function
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

        choice [ pString1; pString2 ] <?> "string"

    let private pLabel =
        pipe2 (skipChar '.') pIdentifier (fun _ label -> label)

    let private pDataValue =
        pipe2 (skipChar '@') pIdentifier (fun _ data -> data)

    let private pSymbol : Parser<ISymbolic,Liyh.Language.Syntax.Indentation.IndentState<unit>> =
        between (skipChar '$') (skipChar '$') (ws >>? Liyh.Language.Syntax.Parser.pExpr)
        |>> fun (symb, _) -> failwithf "TODO" // Liyh.Language.Absyn.cosynToSumProd symb

    let private pRegisterValue =
        pipe2 (skipString "#r" <|> skipChar 'r') pint32
              (fun _ reg -> if reg > MAX_REGISTER then failwithf "the register r%d doesn't exist." reg else reg)

    /// Parse either an integer or a float and return a NumberLiteral.
    let private pNumLit =
        let numFmt =
            NumberLiteralOptions.AllowPlusSign
            ||| NumberLiteralOptions.AllowBinary
            ||| NumberLiteralOptions.AllowHexadecimal
            ||| NumberLiteralOptions.AllowMinusSign
            ||| NumberLiteralOptions.AllowOctal
            ||| NumberLiteralOptions.AllowSuffix

        numberLiteral numFmt "number"

    /// Parse either an integer or a float.
    let private pNumber =
        pNumLit
            |>> function
                | n when n.IsInteger -> Integer(int n.String)
                | _ -> failwithf "<?double?>"
                //| _ -> Float(float nlit.String)

    let private pValue =
        choice
            [ pNumber <?> "a number"
              pLabel <?> "a label's address" |>> Label
              pDataValue <?> "a static data address" |>> Data
              pRegisterValue <?> "a register" |>> Register ]

    type private ILOpcode =
        { opcode': Opcode
          dest': ILValue option
          src': ILValue option
          value': ILValue option }

    let private opcodeK0 opcode _ x = { opcode' = opcode; dest' = Some x; src' = None; value' = None }
    let private opcodeK1 opcode _ x = { opcode' = opcode; dest' = None; src' = None; value' = Some x }
    let private opcodeK2 opcode _ x y = { opcode' = opcode; dest' = Some x; src' = Some y; value' = None }
    let private opcodeK3 opcode _ = { opcode' = opcode; dest' = None; src' = None; value' = None }
    let private opcodeK4 opcode _ x y = { opcode' = opcode; dest' = Some x; src' = None; value' = Some y }

    let private pOpcode =
        let sval = ws1 >>. pValue
        let sint = ws1 >>. pint32 <?> "an integer" |>> Integer
        let sreg = ws1 >>. pRegisterValue <?> "a register" |>> Register
        let slab = ws1 >>. pLabel <?> "a label's address" |>> Label
        let sdat = ws1 >>. pDataValue <?> "a data" |>> Data

        let pprint = pipe2 (skipStringCI "print") sval (opcodeK1 Opcode.PRINT)
        let ppush = pipe2 (skipStringCI "push") sval (opcodeK1 Opcode.PUSH)
        let ppop = pipe2 (skipStringCI "pop") sreg (opcodeK0 Opcode.POP)
        let pcall = pipe2 (skipStringCI "call") sval (opcodeK1 Opcode.CALL)
        let ploadi = pipe3 (skipStringCI "loadi") sreg sint (opcodeK4 Opcode.LOADI)
        let pcmpi = pipe3 (skipStringCI "cmpi") sreg sint (opcodeK4 Opcode.CMPI)
        let pcmp = pipe3 (skipStringCI "cmp") sreg sreg (opcodeK2 Opcode.CMP)
        let padd = pipe3 (skipStringCI "add") sreg sreg (opcodeK2 Opcode.ADD)
        let paddi = pipe3 (skipStringCI "addi") sreg sint (opcodeK4 Opcode.ADDI)
        let pmul = pipe3 (skipStringCI "mul") sreg sreg (opcodeK2 Opcode.MUL)
        let pmuli = pipe3 (skipStringCI "muli") sreg sint (opcodeK4 Opcode.MULI)
        let pdiv = pipe3 (skipStringCI "div") sreg sreg (opcodeK2 Opcode.DIV)
        let pdivi = pipe3 (skipStringCI "divi") sreg sint (opcodeK4 Opcode.DIVI)
        let pmod = pipe3 (skipStringCI "mod") sreg sreg (opcodeK2 Opcode.MOD)
        let pmodi = pipe3 (skipStringCI "modi") sreg sint (opcodeK4 Opcode.MODI)
        let pmov = pipe3 (skipStringCI "mov") sreg sreg (opcodeK2 Opcode.MOV)
        let pmov' = pipe3 (skipStringCI "mov") sreg sdat (opcodeK4 Opcode.MOV)
        let pswap = pipe3 (skipStringCI "swap") sreg sreg (opcodeK2 Opcode.SWAP)
        let phalt = (skipStringCI "halt") |>> (opcodeK3 Opcode.HALT)
        let psti = pipe3 (skipStringCI "sti") sreg sreg (opcodeK2 Opcode.STI)
        let pits = pipe3 (skipStringCI "its") sreg sreg (opcodeK2 Opcode.ITS)
        let pjmp = pipe2 (skipStringCI "jmp") slab (opcodeK1 Opcode.JMP)
        let pjlw = pipe2 (skipStringCI "jlw") slab (opcodeK1 Opcode.JLW)
        let pjlq = pipe2 (skipStringCI "jlq") slab (opcodeK1 Opcode.JLQ)
        let pjgr = pipe2 (skipStringCI "jgr") slab (opcodeK1 Opcode.JGR)
        let pjgq = pipe2 (skipStringCI "jgq") slab (opcodeK1 Opcode.JGQ)
        let pjeq = pipe2 (skipStringCI "jeq") slab (opcodeK1 Opcode.JEQ)
        let pjne = pipe2 (skipStringCI "jne") slab (opcodeK1 Opcode.JNE)
        let pjsr = (skipStringCI "jsr") |>> (opcodeK3 Opcode.JSR)
        let pxor = pipe3 (skipStringCI "xor") sreg sreg (opcodeK2 Opcode.XOR)
        let pret = (skipStringCI "ret") |>> (opcodeK3 Opcode.RET)
        let psqr = pipe2 (skipStringCI "sqr") sreg (opcodeK1 Opcode.SQR)
        let pceil = pipe2 (skipStringCI "ceil") sreg (opcodeK1 Opcode.CEIL)
        let pfloor = pipe2 (skipStringCI "floor") sreg (opcodeK1 Opcode.FLOOR)
        let psrel = pipe2 (skipStringCI "srel") sint (opcodeK1 Opcode.SREL)

        choiceL
            [ pprint; ppush; ppop; pcall; ploadi; pcmpi; pcmp; paddi; padd; pmuli; pmul; attempt pits; psti
            ; attempt pmod; pmodi; pdivi; pdiv; attempt pmov; pmov'; phalt; pjmp; pjlw; pjlq; pjgr; pjgq; pjeq
            ; pswap; pjne; pxor; pret; pjsr; psqr; pceil; pfloor; psrel ]

            "a valid instruction"

    type private ILInstruction =
        | Format of TextKind
        | Opcode of ILOpcode
        | LabelDef of string
        | Entry of string
        | DataDef of string * ILValue
        | Comment

    let private pLabelDef =
        pipe2 pLabel (ws >>. skipChar ':') (fun label _ -> LabelDef label)

    let private pEntry =
        pipe2 (skipStringCI "entry") (ws1 >>. pLabel) (fun _ label -> Entry label)

    let private pFormat =
        pipe2 (skipStringCI "format")
              (ws1 >>. choice [ (skipStringCI "readable" >>% TextKind.Readable); (skipStringCI "executable" >>% TextKind.Executable) ])
              (fun _ format -> Format format)

    let private pDataDef =
        let pStringData = pipe3 (skipStringCI ".string") (ws1 >>. pDataValue) (ws1 >>. pString') (fun _ id str -> id, String str)
        let pSymbolData = pipe3 (skipStringCI ".symbol") (ws1 >>. pDataValue) (ws1 >>. pSymbol) (fun _ id symb -> id, Symbol symb)
        choiceL [ pStringData; pSymbolData ] "A constant data" |>> DataDef

    let private pInstruction =
        choiceL [ pOpcode |>> Opcode; attempt pLabelDef; pDataDef; pFormat; pEntry; pComment >>% Comment ] "a valid instruction"

    let private pProgram =
        many (ws >>. pInstruction .>> many (ws >>. opt pComment >>? newline))

    let private runParserOnFile (path: string) =
        Liyh.Language.Syntax.Indentation.runParserOnFile pProgram () path

    let private clabels (program: ILInstruction list) =

        let rec inner ic acc = function
            | [] -> acc
            | LabelDef str :: xs -> inner (ic + 1) ((str, ic) :: acc) xs
            | _ :: xs -> inner (ic + 1) acc xs

        dict (inner 0 [] program)

    let private cdata (program: ILInstruction list) =

        let rec inner ic acc = function
            | [] -> acc
            | DataDef (name, value) :: xs -> inner (ic + 1) (((name, ic), value) :: acc) xs
            | _ :: xs -> inner ic acc xs

        let a, b = List.unzip (inner 0 [] program)
        dict a, Array.ofList (List.rev b)

    let private getEntry (program: ILInstruction list) (labels: IDictionary<string, int>) =
        let isEntry = function Entry _ -> true | _ -> false

        match List.tryFindBack isEntry program with
        | Some (Entry label) ->
            assert (labels.ContainsKey label)
            labels.[label]
        | _ -> 0

    let private getFormat (program: ILInstruction list) =
        let isFormat = function Format _ -> true | _ -> false

        match List.tryFindBack isFormat program with
        | Some (Format format) -> format
        | _ -> TextKind.Readable

    let private immValue (labels: IDictionary<string, int>) (data: IDictionary<string, int>) = function
        | Integer x -> ImmediateValue.Integer x
        | Label str -> ImmediateValue.Label labels.[str]
        | Data str -> ImmediateValue.Data data.[str]
        | String str -> ImmediateValue.String str
        | Symbol symb -> ImmediateValue.Symbol symb
        | Register x -> ImmediateValue.Register x

    let private dataValue (labels: IDictionary<string, int>) (data: IDictionary<string, int>) = function
        | Integer x -> DataValue.Integer x
        | String str -> DataValue.String str
        | Symbol symb -> DataValue.Symbol symb
        | other -> failwithf "Not a valid Data Value: %s" (string other)

    let private compileInstruction (labels: IDictionary<string, int>) (data: IDictionary<string, int>) = function
        | LabelDef _ -> { opcode = Opcode.LABEL; dest = None; src = None; immValue = None }
        | Entry _ -> { opcode = Opcode.ENTRY; dest = None; src = None; immValue = None }
        | DataDef _ -> { opcode = Opcode.DATA; dest = None; src = None; immValue = None }
        | Format _ -> { opcode = Opcode.FMT; dest = None; src = None; immValue = None }
        | Comment -> failwithf "Invalid instruction: Comment"
        | Opcode { opcode' = opcode'; dest' = dest'; src' = src'; value' = value' } ->

            let creg = function
                | Some (Register x) -> Some x
                | _ -> None

            let copt = Option.map (immValue labels data)

            { opcode = opcode'; dest = creg dest'; src = creg src'; immValue = copt value' }

    let private noComment = function
        | Comment -> false
        | _ -> true

    let private compile (program: ILInstruction list) =
        let program = List.filter noComment program
        let labels = clabels program
        let pdata, data = cdata program
        let format = getFormat program
        let entry = getEntry program labels
        let data = Array.map (dataValue labels pdata) data

        { code  = [| for instr in program -> compileInstruction labels pdata instr |]
          data  = data
          entry = entry
          kind  = format }

    let public compileFile (path: string) =

        match runParserOnFile path with
        | Success (result, _, _) -> Some (compile result)
        | Failure (msg, _, _) -> printfn "%s" msg; None


// AMELIORATIONS: pour optimiser un peu, faire un multi-dictionary pour les .data
// AMELIORATIONS: gérer les flottants

