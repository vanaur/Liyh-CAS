namespace Liyh.Kernel

(* The typical use of a context is as follows: imagine you have an equation and you want to regroup certain terms,
    for example:

            a + aCos[x²] + ac + b² + b²Cos[x²] + b²c - 2 = 0
        <=> (a + b²)(1 + Cos[x²] + c) = 2
        <=> c = 2/(a + b²) - 1 - Cos[x²].

    Then, this operation is only valid if the expression `(a + b²)` is different from zero.
    This condition describes the validity context of the new expression. *)

[<AutoOpen>]
module rec Context =
    open Liyh.Kernel
    open Liyh.Kernel.Equation

    /// An "attribution" is a tag that indicates to which kind of object the expressions or symbols involved belong.
    [<Struct>]
    type public Attribution =
        | Attribution of string

    /// "SumPow If and only If": Describe validity conditions; a context is associated with a SumPow expression
    /// and describes the case in which the expression holds.
    type public SPIFF =
        {
            /// Dictates the equations by which the context holds.
            equations: Equation list

            /// Describes the "types" of the SumPows involved.
            attributions: Map<SumPow, Attribution>
        }

    (* In the general case, it's not possible (or at least very difficult) to know whether a set of arbitrary equations
       is consistent. So we can't decide in the general case whether a context is contradictory, unfortunately. *)

    /// Create a new empty context.
    let public emptySpiff =
        { equations = List.empty; attributions = Map.empty }
    
    /// Check if the given context is filled or not.
    let public isEmptySpiff { equations = equations; attributions = attributions } =
        List.isEmpty equations && Map.isEmpty attributions
    
