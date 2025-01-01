namespace Liyh.Language.Evaluation

module VirtualMachine =
    open System
    open System.Collections.Generic
    open Liyh.Kernel
    open Liyh.Utils
    open Liyh.Language.Evaluation.IL

    exception private IncompatibleAdditionException of EvalValue * EvalValue
    exception private IncompatibleMultiplicationException of EvalValue * EvalValue
    exception private IncompatibleDivisionException of EvalValue * EvalValue
    exception private InvalidInstructionException of Instruction
    exception private InvalidSymbolException of EvalValue
    exception private InvalidSquareException of EvalValue
    exception private InvalidCeilException of EvalValue
    exception private InvalidFloorException of EvalValue
    exception private InvalidEncodingException of path: string

    [<RequireQualifiedAccess>]
    module private ILArith =

        let inline public addition (v1: EvalValue) (v2: EvalValue) =
            match (v1, v2) with
            | EvalValue.Integer a, EvalValue.Integer b -> EvalValue.Integer(a + b)
            | EvalValue.Symbol(:? Symbol as { atom = Atom.Const a }),
              EvalValue.Symbol(:? Symbol as { atom = Atom.Const b }) ->
                EvalValue.Symbol
                    { atom = Atom.Const(a + b)
                      attributes = [] }
            | EvalValue.Double a, EvalValue.Double b -> EvalValue.Double(a + b)
            | EvalValue.Double a, EvalValue.Integer b -> EvalValue.Double(a + double b)
            | EvalValue.Integer a, EvalValue.Double b -> EvalValue.Double(double a + b)
            | _ -> raise (IncompatibleAdditionException(v1, v2))

        let inline public multiplication (v1: EvalValue) (v2: EvalValue) =
            match (v1, v2) with
            | EvalValue.Integer a, EvalValue.Integer b -> EvalValue.Integer(a * b)
            | EvalValue.Symbol(:? Symbol as { atom = Atom.Const a }),
              EvalValue.Symbol(:? Symbol as { atom = Atom.Const b }) ->
                EvalValue.Symbol
                    { atom = Atom.Const(a * b)
                      attributes = [] }
            | EvalValue.Double a, EvalValue.Double b -> EvalValue.Double(a * b)
            | EvalValue.Double a, EvalValue.Integer b -> EvalValue.Double(a * double b)
            | EvalValue.Integer a, EvalValue.Double b -> EvalValue.Double(double a * b)
            | _ -> raise (IncompatibleMultiplicationException(v1, v2))

        let inline public division (v1: EvalValue) (v2: EvalValue) =
            match (v1, v2) with
            | EvalValue.Integer a, EvalValue.Integer b -> EvalValue.Integer(a / b)
            | EvalValue.Symbol(:? Symbol as { atom = Atom.Const a }),
              EvalValue.Symbol(:? Symbol as { atom = Atom.Const b }) ->
                if Constant.isZero b then
                    EvalValue.Null
                else
                    EvalValue.Symbol
                        { atom = Atom.Const(a / b)
                          attributes = [] }
            | EvalValue.Double a, EvalValue.Double b -> EvalValue.Double(a / b)
            | EvalValue.Double a, EvalValue.Integer b -> EvalValue.Double(a / double b)
            | EvalValue.Integer a, EvalValue.Double b -> EvalValue.Double(double a / b)
            | _ -> raise (IncompatibleDivisionException(v1, v2))

        let inline public modulo (v1: EvalValue) (v2: EvalValue) =
            match (v1, v2) with
            | EvalValue.Integer a, EvalValue.Integer b -> EvalValue.Integer(a % b)
            | EvalValue.Double a, EvalValue.Double b -> EvalValue.Double(a % b)
            | EvalValue.Double a, EvalValue.Integer b -> EvalValue.Double(a % double b)
            | EvalValue.Integer a, EvalValue.Double b -> EvalValue.Double(double a % b)
            | _ -> raise (IncompatibleDivisionException(v1, v2))

        let inline public xor (v1: EvalValue) (v2: EvalValue) =
            if v1 = v2 then
                (EvalValue.Integer 0)
            else
                (EvalValue.Integer 1)

        let public sqr =
            function
            | EvalValue.Integer a -> EvalValue.Double(sqrt (double a))
            | EvalValue.Double a -> EvalValue.Double(sqrt a)
            | v -> raise (InvalidSquareException v)

        let public ceil =
            function
            | EvalValue.Integer a -> EvalValue.Integer a
            | EvalValue.Double a -> EvalValue.Integer(int (System.Math.Ceiling(float a)))
            | v -> raise (InvalidCeilException v)

        let public floor =
            function
            | EvalValue.Integer a -> EvalValue.Integer a
            | EvalValue.Double a -> EvalValue.Integer(int (System.Math.Floor a))
            | v -> raise (InvalidFloorException v)

    [<RequireQualifiedAccess>]
    module private ILFlag =

        [<Struct>]
        type public Flag =
            | LW = 0 // Lower
            | LQ = 1 // Lower or equal
            | GR = 2 // Greater
            | GQ = 3 // Greater or equal
            | EQ = 4 // Equal
            | NE = 5 // Not equal
            | UD = 6 // Undefined

        let inline public setFlag (v1: int) (v2: int) : Flag =
            match v1.CompareTo v2 with
            | -1 -> Flag.LW
            | 0 -> Flag.EQ
            | 1 -> Flag.GR
            | _ -> Flag.UD

        let inline public isLQ (flag: Flag) =
            (flag = Flag.LQ) || (flag = Flag.EQ) || (flag = Flag.LW)

        let inline public isGQ (flag: Flag) =
            (flag = Flag.GQ) || (flag = Flag.EQ) || (flag = Flag.GR)

        let inline public isLW (flag: Flag) = (flag = Flag.LW)
        let inline public isGR (flag: Flag) = (flag = Flag.GR)
        let inline public isEQ (flag: Flag) = (flag = Flag.EQ)
        let inline public isNE (flag: Flag) = (flag <> Flag.EQ)

    [<Struct>]
    type private EvalState =
        { stack: EvalValue Stack
          registers: EvalValue array
          mutable flag: ILFlag.Flag
          mutable pc: int
          mutable running: bool }

    let private dataValueToEvalValue =
        function
        | DataValue.Double double -> EvalValue.Double double
        | DataValue.Integer integer -> EvalValue.Integer integer
        | DataValue.String string -> EvalValue.String string
        | DataValue.Symbol symbolic -> EvalValue.Symbol symbolic

    let inline private immValueToEvalValue (data: DataValue array) (registers: EvalValue array) =
        function
        | ImmediateValue.Data address -> dataValueToEvalValue data.[address]
        | ImmediateValue.Double double -> EvalValue.Double double
        | ImmediateValue.Integer integer -> EvalValue.Integer integer
        | ImmediateValue.Label labelAddress -> EvalValue.Label labelAddress
        | ImmediateValue.String string -> EvalValue.String string
        | ImmediateValue.Symbol symbolic -> EvalValue.Symbol symbolic
        | ImmediateValue.Register register -> registers.[register]
        | ImmediateValue.Null -> failwith "May not happen"

    let inline private eval (program: Program inref) (state: EvalState byref) (instr: Instruction) =
        let immToEv = immValueToEvalValue program.data state.registers

        match instr with
        | { opcode = Opcode.LABEL } -> ()
        | { opcode = Opcode.ENTRY } -> ()
        | { opcode = Opcode.DATA } -> ()

        // PUSH VALUE{}
        | { opcode = Opcode.PUSH
            immValue = Some value } ->

            state.stack.Push(immToEv value)

        // POP DEST
        | { opcode = Opcode.POP
            dest = Some dest } ->

            state.registers.[dest] <- state.stack.Pop()

        // LOADI DEST VALUE{Integer}
        | { opcode = Opcode.LOADI
            dest = Some dest
            immValue = Some((ImmediateValue.Integer _) as value) } ->

            state.registers.[dest] <- immToEv value

        // CMPI SRC VALUE{Integer}
        | { opcode = Opcode.CMPI
            dest = Some dest
            immValue = Some(ImmediateValue.Integer value) } ->

            match state.registers.[dest] with
            | EvalValue.Integer x -> state.flag <- ILFlag.setFlag x value
            | _ -> failwithf "Invalid integer: %A in r%d register" state.registers.[dest] dest

        // CMP DEST SRC
        | { opcode = Opcode.CMP
            dest = Some dest
            src = Some src } ->

            match state.registers.[dest], state.registers.[src] with
            | EvalValue.Integer x, EvalValue.Integer y -> state.flag <- ILFlag.setFlag x y
            | instr -> failwithf "Invalid comparaison: %A" instr

        // CALL VALUE{Label, Register}
        | { opcode = Opcode.CALL
            immValue = Some(ImmediateValue.Register label) }

        | { opcode = Opcode.CALL
            immValue = Some(ImmediateValue.Label label) } ->

            state.stack.Push(EvalValue.Label state.pc)
            state.pc <- label

        // RET
        | { opcode = Opcode.RET } ->

            let mutable value = EvalValue.Label -1

            if state.stack.TryPop &value then
                match value with
                | EvalValue.Label address -> state.pc <- address
                | other -> failwithf "`%s` is not a valid RET address." (string other)

        // JEQ VALUE{Label, Register}
        | { opcode = Opcode.JEQ
            immValue = Some(ImmediateValue.Register label) }

        | { opcode = Opcode.JEQ
            immValue = Some(ImmediateValue.Label label) } ->

            if ILFlag.isEQ state.flag then
                state.pc <- label

            state.flag <- ILFlag.Flag.UD

        // JGQ VALUE{Label, Register}
        | { opcode = Opcode.JGQ
            immValue = Some(ImmediateValue.Register label) }

        | { opcode = Opcode.JGQ
            immValue = Some(ImmediateValue.Label label) } ->

            if ILFlag.isGQ state.flag then
                state.pc <- label

            state.flag <- ILFlag.Flag.UD

        // JGR VALUE{Label, Register}
        | { opcode = Opcode.JGR
            immValue = Some(ImmediateValue.Register label) }

        | { opcode = Opcode.JGR
            immValue = Some(ImmediateValue.Label label) } ->

            if ILFlag.isGR state.flag then
                state.pc <- label

            state.flag <- ILFlag.Flag.UD

        // JLQ VALUE{Label, Register}
        | { opcode = Opcode.JLQ
            immValue = Some(ImmediateValue.Register label) }

        | { opcode = Opcode.JLQ
            immValue = Some(ImmediateValue.Label label) } ->

            if ILFlag.isLQ state.flag then
                state.pc <- label

            state.flag <- ILFlag.Flag.UD

        // JLW VALUE{Label, Register}
        | { opcode = Opcode.JLW
            immValue = Some(ImmediateValue.Register label) }

        | { opcode = Opcode.JLW
            immValue = Some(ImmediateValue.Label label) } ->

            if ILFlag.isLW state.flag then
                state.pc <- label

            state.flag <- ILFlag.Flag.UD

        // JNE VALUE{Label, Register}
        | { opcode = Opcode.JNE
            immValue = Some(ImmediateValue.Register label) }

        | { opcode = Opcode.JNE
            immValue = Some(ImmediateValue.Label label) } ->

            if ILFlag.isNE state.flag then
                state.pc <- label

            state.flag <- ILFlag.Flag.UD

        // STI DEST SRC
        | { opcode = Opcode.STI
            dest = Some dest
            src = Some src } ->

            match state.registers.[src] with
            | EvalValue.Symbol(:? Symbol as { atom = Atom.Const x }) ->
                state.registers.[dest] <- EvalValue.Integer(Constant.toInt x)
            | s -> raise (InvalidSymbolException s)

        // ITS DEST SRC
        | { opcode = Opcode.ITS
            dest = Some dest
            src = Some src } ->

            match state.registers.[src] with
            | EvalValue.Integer value ->
                state.registers.[dest] <-
                    EvalValue.Symbol
                        { atom = Atom.Const(Constant value)
                          attributes = [] }
            | s -> raise (InvalidSymbolException s)

        // ADD DEST SRC
        | { opcode = Opcode.ADD
            dest = Some dest
            src = Some src } ->

            state.registers.[dest] <- ILArith.addition state.registers.[dest] state.registers.[src]

        // ADDI DEST VALUE{Integer}
        | { opcode = Opcode.ADDI
            dest = Some dest
            immValue = Some value } ->

            state.registers.[dest] <- ILArith.addition state.registers.[dest] (immToEv value)

        // MULI VALUE{Integer}
        | { opcode = Opcode.MULI
            dest = Some dest
            immValue = Some value } ->

            state.registers.[dest] <- ILArith.multiplication state.registers.[dest] (immToEv value)

        // MUL DEST SRC
        | { opcode = Opcode.MUL
            dest = Some dest
            src = Some src } ->

            state.registers.[dest] <- ILArith.multiplication state.registers.[dest] state.registers.[src]

        // DIVI DEST VALUE{Integer}
        | { opcode = Opcode.DIVI
            dest = Some dest
            immValue = Some value } ->

            state.registers.[dest] <- ILArith.division state.registers.[dest] (immToEv value)

        // DIV DEST SRC
        | { opcode = Opcode.DIV
            dest = Some dest
            src = Some src } ->

            state.registers.[dest] <- ILArith.division state.registers.[dest] state.registers.[src]

        // MODI DEST VALUE{Integer}
        | { opcode = Opcode.MODI
            dest = Some dest
            immValue = Some value } ->

            state.registers.[dest] <- ILArith.modulo state.registers.[dest] (immToEv value)

        // MOD DEST SRC
        | { opcode = Opcode.MOD
            dest = Some dest
            src = Some src } ->

            state.registers.[dest] <- ILArith.modulo state.registers.[dest] state.registers.[src]

        // SQR DEST
        | { opcode = Opcode.SQR
            dest = Some dest } ->

            state.registers.[dest] <- ILArith.sqr state.registers.[dest]

        // MOV DEST SRC
        | { opcode = Opcode.MOV
            dest = Some dest
            src = Some src } ->

            state.registers.[dest] <- state.registers.[src]

        // MOV DEST VALUE{Data}
        | { opcode = Opcode.MOV
            dest = Some dest
            immValue = Some(ImmediateValue.Data k) } ->

            state.registers.[dest] <- dataValueToEvalValue program.data.[k]

        // SWAP DEST SRC
        | { opcode = Opcode.SWAP
            dest = Some dest
            src = Some src } ->

            let temp = state.registers.[dest]
            state.registers.[dest] <- state.registers.[src]
            state.registers.[src] <- temp

        // XOR DEST SRC
        | { opcode = Opcode.XOR
            dest = Some dest
            src = Some src } ->

            state.registers.[dest] <- ILArith.xor state.registers.[dest] state.registers.[src]

        // JMP VALUE{Label, Registeer}
        | { opcode = Opcode.JMP
            immValue = Some(ImmediateValue.Register label) }

        | { opcode = Opcode.JMP
            immValue = Some(ImmediateValue.Label label) } ->

            state.pc <- label

        // CEIL DEST
        | { opcode = Opcode.CEIL
            dest = Some dest } ->

            state.registers.[dest] <- ILArith.ceil state.registers.[dest]

        // FLOOR DEST
        | { opcode = Opcode.FLOOR
            dest = Some dest } ->

            state.registers.[dest] <- ILArith.floor state.registers.[dest]

        // SREL VALUE{Integer}
        | { opcode = Opcode.SREL
            immValue = Some(ImmediateValue.Integer r) } ->

            for _ = 1 to r do
                state.stack.Pop() |> ignore

        // JSR
        | { opcode = Opcode.JSR } ->

            let mutable value = EvalValue.Label -1

            if state.stack.TryPop &value then
                match value with
                | EvalValue.Label address ->
                    state.stack.Push(EvalValue.Label state.pc)
                    state.pc <- address
                | other -> failwithf "`%s` is not a valid subroutine address." (string other)

        // HALT
        | { opcode = Opcode.HALT } ->

            state.running <- false

        // PRINT VALUE{}
        | { opcode = Opcode.PRINT
            immValue = Some value } ->

            match value with
            | ImmediateValue.Register reg -> printfn "#r%d = %A" reg state.registers.[reg]
            | ImmediateValue.Label label -> printfn "@%d" label
            | ImmediateValue.Integer x -> printfn "%d" x
            | ImmediateValue.Double x -> printfn "%g" x
            | ImmediateValue.String s -> printfn " %s" s
            | ImmediateValue.Data d -> printfn "%A" program.data.[d]
            | ImmediateValue.Symbol sp -> printfn "%A" sp
            | ImmediateValue.Null -> printfn ""

        // Unexpected
        | instr ->
            printfn "EXN: %A" instr
            raise (InvalidInstructionException instr)

    let private newState { entry = entry } =
        { stack = Stack<EvalValue>(12) (* initial capacity is set to 12, but it can grow further *)
          registers = Array.init MAX_REGISTER (konst EvalValue.Null)
          flag = ILFlag.Flag.UD
          pc = entry
          running = false }

    let inline private advance (program: Program inref) (state: EvalState byref) (instr: Instruction) =
        eval &program &state instr
        state.pc <- state.pc + 1

    let inline private run (program: Program inref) (state: EvalState byref) =
        state.running <- true

        while (state.running && state.pc < program.code.Length) do
            advance &program &state program.code.[state.pc]

        state.running <- false

    module private CompiledByteCode =
        open ByteDev.Encoding.Hex
        open ByteDev.Encoding.Serialization

        let private serializer = Serializer(HexEncoder())

        let private hexDecode (path: string) (text: string) =
            if not (text.IsHex()) then
                raise (InvalidEncodingException path)

            serializer.Deserialize<Program>(text)

        let public decodeFile (path: string) =
            let text = System.IO.File.ReadAllText path
            hexDecode path text

        let public decodeString (text: string) = hexDecode null text

    type public LiyhVM(program: Program) =
        let mutable state = newState program
        let sw = Diagnostics.Stopwatch()

        new(hexProgram: string, isFromFile: bool) =
            if isFromFile then
                LiyhVM(CompiledByteCode.decodeFile hexProgram)
            else
                LiyhVM(CompiledByteCode.decodeString hexProgram)

        new(code: Instruction array, data: DataValue array, entry: int) =
            LiyhVM
                { code = code
                  data = data
                  entry = entry
                  kind = TextKind.Executable }

        new(code: Instruction array, data: DataValue array) =
            LiyhVM
                { code = code
                  data = data
                  entry = -1
                  kind = TextKind.Readable }

        member public __.ExecutionTime = sw.Elapsed

        member public __.GetState() =
            {| stack = state.stack
               registers = state.registers
               running = state.running |}

        member public __.Run() =
            GC.Collect()
            sw.Start()

            match program.kind with
            | TextKind.Executable -> run &program &state
            | TextKind.Readable -> ()

            sw.Stop()

        member public __.AsyncRun() =
            sw.Start() // Le stop??

            match program.kind with
            | TextKind.Executable -> async { advance &program &state program.code.[state.pc] }
            | TextKind.Readable -> async.Zero()

        member public __.Pause() =
            state.running <- false
            sw.Stop()



// Il faurait aussi faire un dictionnaire des labels typiquement pour une library

// Il serait intéressant d'avoir des registres vectoriels
// et des instructions vectoriels !!
// Cela permet deux choses :
//  - Faire du SIMD
//  - Avoir des "mini-tableaux"-like
// https://github.com/giladfrid009/SimpleSIMD
//
// Il faudrait également un registre qui pointe vers le flag (avec seulement true/false)
// Et pour la pile


(*
Il nous fait une nouvelle instruction qui prend un registre R et qui converti sa représentation en ISymbolic

symb r0 r0      <- ça met dans r0 le résultat de la conversion

par exemple, si r0 est SumPow alors symb r0 r0 met dans r0 ISymbolic


____

Il faut aussi définir des "labels virtuels" qui font références aux moteurs ou fonctions à exécuter ?
On les prend dans les négatifs (sauf -1 qui est réservé pour 'erreur')


*)

// https://stackoverflow.com/questions/5655936/how-to-use-c-cli-within-c-sharp-application


// Sur le fonctionnement des VM à registre et tout
//  - https://www.recurse.com/blog/7-understanding-c-by-learning-assembly
//  - https://zhu45.org/posts/2017/Jul/30/understanding-how-function-call-works/
//  - https://en.m.wikibooks.org/wiki/X86_Disassembly/Functions_and_Stack_Frames
//  - https://www.bartoszsypytkowski.com/simple-virtual-machine/
