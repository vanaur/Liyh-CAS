namespace Liyh.Language.Evaluation

module Hex =
    open System.IO
    open System.Collections.Generic
    open Liyh.Utils
    open Liyh.Kernel.SumPow
    open Liyh.Language.Evaluation.IL
    open ByteDev.Encoding

    //  * I : integer
    //  * F : float
    //  * S : string
    //  * Y : symbol
    //  * R_: register _

    [<Struct>]
    type public OpCode =

        (* PCALL_: Calls a labeled procedure. The return type is specified (I, F, S, E) and the
                   return value is stored in the given register.

           Usage: pcall_ _DEST
        *)

        | PCALLI
        | PCALLF
        | PCALLS
        | PCALLE

        (* LOAD_: Loads an immediate value of the specified type into the specified register.

           Usage: load_ _DEST 
        *)

        | LOADI
        | LOADF
        | LOADS
        | LOADE

        (* CMP_: Performs a comparison of the specified type on a register and a given immediate value.

           Usage: cmp_ _REG
        *)

        | CMPI
        | CMPF
        | CMPS
        | CMPE

        (* CMPR_: Performs a comparison of the specified type on a register and another register of the same type.

           Usage: cmpr_ _REG
        *)

        | CMPRI
        | CMPRF
        | CMPRS
        | CMPRE

        (* Basic arithmetic (ADD_, MUL_, DIV_, MOD_)
           
           Usage: ADD_/MUL_/DIV_/MOD_ DEST SRC
        *)

        | ADDI
        | ADDF
        
        | ADDRI
        | ADDRF

        | MULI
        | MULF
        
        | MULRI
        | MULRF

        | DIVI
        | DIVF

        | DIVRI
        | DIVRF

        | MODI
        | MODF

        | MODRI
        | MODRF

        (* CATS: Concatenates the immediate string given at the end of the given register of the string type.

           Usage: cats DEST imm
        *)

        | CATS

        (* CATRS: Concatenates the two string registers.

           Usage: catrs DEST SRC
        *)

        | CATRS

        (* MOV_: Copies the contents of a register of the specified type to a register of the same type.

           Usage: mov_ DEST SRC
        *)

        | MOVI
        | MOVF
        | MOVS
        | MOVE

        (* FROM_: Converts the given integer/float/string immediate value into a symbol and stores it in the
                  specified symbolic register.
        
           Usage: from_ DEST imm
        *)

        | FROMI
        | FROMF
        | FROMS

        (* TO_: Converts the given symbolic immediate value into an integer/float/string and stores it in the
                specified integer/float/string register.
        
           Usage: to_ DEST imm
        *)

        | TOI
        | TOF
        | TOS

        (* J__ to the specified label depending on the flag.

           Usage: j__ .label
        *)

        | JMP
        | JLW
        | JLQ
        | JGR
        | JGQ
        | JEQ
        | JNE

        (* RET_: Transfers program control to the return address and store the given immediate specified
                 value for the caller.
        
           Usage: ret_ imm
        *)

        | RETI
        | RETF
        | RETS
        | RETE

        (* RETR_: Transfers program control to the return address and store the given register's value
                  for the caller.
           
           Usage: retr_ SRC
        *)

        | RETRI
        | RETRF
        | RETRS
        | RETRE

        | SWAPRI
        | SWAPRF
        | SWAPRS
        | SWAPRE


(*

    .example:
      addri i0 i1
      addri i0 i2
      addri i0 i3

      retri i0

    .main:
      loadi i0 5
      loadi i1 3
      loadi i2 7
      loadi i3 2

      callri i0
      reti 0


*)



// On va utiliser un nombre de registres infini.
// Les arguments d'une procédure sont les premiers registres.
// Par exemple, Foo[a, b, c] => i0 = a, i1 = b, i2 = c.


// let bw = new BinaryWriter(File.OpenWrite("TEST.bin"))
// bw.Write(0x76)
// bw.Write(0x83)
// bw.Write("Hello")
// bw.Write(0x00)
// bw.Close()
// 
// let br = new BinaryReader(File.OpenRead("TEST.bin"))
// printfn "%A" <| br.Read()