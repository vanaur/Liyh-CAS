namespace Liyh.Language.Evaluation

module rec IL =
    open Liyh.Kernel
    open System.ComponentModel

    [<Struct; RequireQualifiedAccess>]
    type public ImmediateValue =
        | Label of labelAddress: int
        | Data of dataAddress: int
        | Register of register: int
        | Integer of integer: int
        | Double of double: double
        | String of string: string
        | Symbol of symbolic: ISymbolic
        | Null

    [<Struct; RequireQualifiedAccess>]
    type public EvalValue =
        | Label of labelAddress: int
        | Integer of integer: int
        | Double of double: double
        | String of string: string
        | Symbol of symbolic: ISymbolic
        | Null

    [<Struct; RequireQualifiedAccess>]
    type public DataValue =
        | Integer of integer: int
        | Double of double: double
        | String of string: string
        | Symbol of symbolic: ISymbolic

    /// An instruction consists of 4 parameters: the opcode, which determines the instruction, a destination
    /// register, a source register and an immediate value. Not all of these parameters are always used.
    [<Struct; ReadOnly(true)>]
    type public Instruction =
        { opcode: Opcode                    // The opcode instruction
          dest: int option                  // The destination register
          src: int option                   // The source register
          immValue: ImmediateValue option } // The immediate value

    [<Struct>]
    type public Opcode =
        | PRINT = 0x0   //  print VALUE         -- display the value, for debug purpose
        | PUSH = 0x1    //  push VALUE          -- push the value onto the stack
        | POP = 0x2     //  pop DEST            -- pop the stack onto the DEST register  
        | CALL = 0x3    //  call FN             -- call the builtin function FN
        | LOADI = 0x4   //  loadi DEST VALUE    -- load the value onto the DEST register
        | CMPI = 0x5    //  cmpi SRC VALUE      -- compare the SRC register with the value and update the flag
        | CMP = 0x6     //  cmp DEST SRC        -- compare the two registers and update the flag
        | ADD = 0x7     //  add DEST SRC        -- add the two registers and store the result in DEST
        | ADDI = 0x8    //  addi DEST VALUE     -- add the integer value to the DEST register
        | MUL = 0x9     //  mul DEST SRC        -- multiply the two registers and store the result in DEST 
        | MULI = 0xA    //  muli DEST VALUE     -- multiply the integer value to the DEST regiser
        | DIV = 0xB     //  div DEST SRC        -- divise the two registers and store the result in DEST
        | DIVI = 0xC    //  divi DEST SRC       -- divise the register content with the given integer
        | MOD = 0xD     //  mod DEST SRC        -- modulo the two registers and store the result in DEST
        | MODI = 0xE    //  modi DEST SRC       -- modulo the register content with the given integer
        | MOV = 0xF     //  mov DEST SRC        -- copy the SRC register into the DEST register
        | SWAP = 0x10   //  swap DEST SRC       -- swap the given registers' value
        | LABEL = 0x11  //  .label              -- indicate a jump label
        | ENTRY = 0x12  //  entry ADDRESS       -- indicate the entry point
        | DATA = 0x13   //  .data NAME data     -- define a new constant data
        | HALT = 0x14   //  halt                -- stop the evaluation
        | STI = 0x15    //  STI DEST SRC        -- cast the SRC register value (expected to be symbol) to an integer
        | ITS = 0x16    //  ITS DEST SRC        -- cast the SRC register value (expected to be an int) to a symbol
        | JMP = 0x17    //  jmp ADDRESS         -- unconditional jump to the given label
        | JLW = 0x18    //  jlw ADDRESS         -- if the flag is set to LW then jump to the given label
        | JLQ = 0x19    //  jlq ADDRESS         -- if the flag is set to LQ then jump to the given label
        | JGR = 0x1A    //  jgr ADDRESS         -- if the flag is set to GR then jump to the given label
        | JGQ = 0x1B    //  jgq ADDRESS         -- if the flag is set to GQ then jump to the given label
        | JEQ = 0x1C    //  jeq ADDRESS         -- if the flag is set to EQ then jump to the given label 
        | JNE = 0x1D    //  jne ADDRESS         -- if the flag is set to NE then jump to the given label
        | FMT = 0x1E    //  format FMT          -- specifies whether the program is an executable or a library
        | RET = 0x1F    //  ret                 -- 
        | JSR = 0x20    //  jsr                 -- jumps to the address at the top of the stack and pushes the program state into the stack
        | XOR = 0x21    //  xor DEST SRC        -- xor the given registers
        | SQR = 0x22    //  sqr DEST            -- Take the square root of the DEST register
        | CEIL = 0x23   //  ceil DEST           -- ceil the given register (Integer or Float) and cast it into an Integer
        | FLOOR = 0x24  //  floor DEST          -- floor the given register (Integer or Float) and cast it into a Float
        | SREL = 0x25   //  srel INTEGER        -- frees the stack of n elements (starting from the top of the stack)

    /// The number of register is fixed.
    let [<Literal>] public MAX_REGISTER = 8

    let private showInstruction pc { opcode = opcode; dest = dest; src = src; immValue = value } =

        match opcode with
        | Opcode.LABEL -> sprintf "\n.l%d:\n" pc
        | Opcode.ENTRY | Opcode.DATA -> ""
        | Opcode.FMT -> "format readable"
        | _ ->
            let showOpcode = (string opcode).ToLower()
            let showDest = if dest.IsSome then sprintf "#r%d " dest.Value else ""
            let showSrc = if src.IsSome then sprintf "#r%d " src.Value else ""
            let showValue = if value.IsSome then sprintf "%s " (showImmValue value.Value) else ""

            sprintf "  %s %s%s%s\n" showOpcode showDest showSrc showValue

    let private showData dc = function
        | DataValue.String x -> sprintf ".string @d%d \"%s\"" dc (string x)
        | DataValue.Symbol x -> sprintf ".symbol @d%d $%s$" dc (string x)
        | _ -> "<??>"

    let private showImmValue = function
        | ImmediateValue.Null -> "NULL"
        | ImmediateValue.Label x -> sprintf ".l%d" x
        | ImmediateValue.Data x -> sprintf "@d%d" x
        | ImmediateValue.Register x -> sprintf "#r%d" x
        | ImmediateValue.Integer x -> sprintf "0x%s" (System.Convert.ToString(x, 16))  // BUG! -1 converted to 0xffffffff
        | ImmediateValue.Double x -> sprintf "%g" x
        | ImmediateValue.String x -> string x
        | ImmediateValue.Symbol x -> string x

    /// Generates an ASM-like representation of the generated IL.
    //let public showILProgram (program: Instruction array) (data: Value array) (entry: int) =
    let public showILProgram { code = program; data = data; entry = entry } =
        let showData = data |> Array.mapi showData |> String.concat "\n"
        let showProgram = program |> Array.mapi showInstruction |> String.concat ""
        let showEntry = sprintf "entry .l%d" entry

        let initMsg = ";\n; IL code generated by Liyh's compiler!\n;\n\n"

        sprintf "%s%s%s%s%s\n%s"
            initMsg
            showEntry
            (if not (Array.isEmpty data) then "\n\n" else "")
            showData
            (if not (Array.isEmpty data) then "\n" else "")
            showProgram

    [<RequireQualifiedAccess>]
    type public TextKind =
        | Executable    // For programs
        | Readable      // For libraries

    type public Program =
        { code: Instruction array
          data: DataValue array
          entry: int
          kind: TextKind }

    [<RequireQualifiedAccess>]
    module public Patterns =

        let public (|FValue|FDest|FDestValue|FDestSrc|FSrcValue|FVoid|Unexpected|) = function
            | { opcode = Opcode.PRINT; immValue = Some value } -> FValue (Opcode.PRINT, value)
            | { opcode = Opcode.PUSH; immValue = Some value } -> FValue (Opcode.PUSH, value)
            | { opcode = Opcode.POP; dest = Some dest } -> FDest (Opcode.POP, dest)
            | { opcode = Opcode.CALL; immValue = Some value } -> FValue (Opcode.CALL, value)
            | { opcode = Opcode.LOADI; dest = Some dest; immValue = Some value } -> FDestValue (Opcode.LOADI, dest, value)
            | { opcode = Opcode.CMPI; src = Some src; immValue = Some value } -> FSrcValue (Opcode.LOADI, src, value)
            | { opcode = Opcode.CMP; dest = Some dest; src = Some src } -> FDestSrc (Opcode.CMP, dest, src)
            | { opcode = Opcode.ADD; dest = Some dest; src = Some src } -> FDestSrc (Opcode.ADD, dest, src) 
            | { opcode = Opcode.ADDI; dest = Some dest; immValue = Some value } -> FDestValue (Opcode.ADDI, dest, value)
            | { opcode = Opcode.MUL; dest = Some dest; src = Some src } -> FDestSrc (Opcode.MUL, dest, src) 
            | { opcode = Opcode.MULI; dest = Some dest; immValue = Some value } -> FDestValue (Opcode.MULI, dest, value)
            | { opcode = Opcode.DIV; dest = Some dest; src = Some src } -> FDestSrc (Opcode.DIV, dest, src) 
            | { opcode = Opcode.DIVI; dest = Some dest; immValue = Some value } -> FDestValue (Opcode.DIVI, dest, value)
            | { opcode = Opcode.MOD; dest = Some dest; src = Some src } -> FDestSrc (Opcode.MOD, dest, src) 
            | { opcode = Opcode.MODI; dest = Some dest; immValue = Some value } -> FDestValue (Opcode.MODI, dest, value)
            | { opcode = Opcode.MOV; dest = Some dest; src = Some src } -> FDestSrc (Opcode.MOV, dest, src) 
            | { opcode = Opcode.SWAP; dest = Some dest; src = Some src } -> FDestSrc (Opcode.SWAP, dest, src) 
            | { opcode = Opcode.LABEL } -> FVoid Opcode.LABEL
            | { opcode = Opcode.ENTRY } -> FVoid Opcode.ENTRY
            | { opcode = Opcode.DATA } -> FVoid Opcode.DATA
            | { opcode = Opcode.HALT } -> FVoid Opcode.HALT
            | { opcode = Opcode.STI; dest = Some dest; src = Some src } -> FDestSrc (Opcode.STI, dest, src)
            | { opcode = Opcode.ITS; dest = Some dest; src = Some src } -> FDestSrc (Opcode.ITS, dest, src)
            | { opcode = Opcode.JMP; immValue = Some value } -> FValue (Opcode.JMP, value)
            | { opcode = Opcode.JLW; immValue = Some value } -> FValue (Opcode.JLW, value)  
            | { opcode = Opcode.JLQ; immValue = Some value } -> FValue (Opcode.JLQ, value)  
            | { opcode = Opcode.JGR; immValue = Some value } -> FValue (Opcode.JGR, value)  
            | { opcode = Opcode.JGQ; immValue = Some value } -> FValue (Opcode.JGQ, value)  
            | { opcode = Opcode.JEQ; immValue = Some value } -> FValue (Opcode.JEQ, value)  
            | { opcode = Opcode.JNE; immValue = Some value } -> FValue (Opcode.JNE, value)  
            | { opcode = Opcode.FMT }  -> FVoid Opcode.FMT
            | instr -> Unexpected instr
