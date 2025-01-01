namespace Liyh.Kernel

[<AutoOpen>]
module rec Constant =
    open Liyh.Utils
    open System

    /// A numerical constant is a wrapper around `double`.
    type public Constant =
        | Constant of constant: double

        member public this.IsZero = isZero this
        member public this.IsOne = isOne this

        override this.ToString() = showConstant -1 this

        static member op_Addition(Constant a, Constant b) = Constant(a + b)
        static member op_Subtraction(Constant a, Constant b) = Constant(a - b)
        static member op_Multiply(Constant a, Constant b) = Constant(a * b)
        static member op_Division(Constant a, Constant b) = Constant(a / b)
        static member Pow(Constant a, Constant b) = Constant(a ** b)
        static member op_UnaryNegation(Constant a) = Constant -a
        static member op_Range(Constant a, Constant b) = [| a..b |] |> Array.map Constant
        static member op_RangeStep(Constant a, Constant step, Constant b) = [| a..step..b |] |> Array.map Constant

        static member op_Implicit(x: int) = Constant x
        static member op_Implicit(x: double) = Constant x

        static member Zero = Zero
        static member One = One

    let public Zero = Constant 0
    let public One = Constant 1

    /// Displays the constant with the given number of significant digits.
    /// Note: precision and accuracy are two different things! Constant is subject to `double` capabilities.
    let public showConstant (precision: int) (Constant cst) =
        if precision <= 0 then sprintf "%g" cst else sprintf "%.*g" precision cst

    let inline public fromBigInt (a: bigint) = Constant(double a)
    let inline public fromDouble (a: double) = Constant(a)

    /// An active pattern to match the constant to a `bigint` (within the precision limits of `double`).
    let inline public (|CBigInteger|_|) (Constant cst) =
        if abs (cst % 1.) <= Double.Epsilon * 100. then Some(bigint cst)
        else None

    /// An active pattern to match the constant to a `int` (within the precision limits of `double`).
    let inline public (|CInteger|_|) (Constant cst) =
        if abs (cst % 1.) <= Double.Epsilon * 100. then Some(int cst)
        else None

    /// An active pattern to match the constant to a floating-point number (using the `double` precision).
    let public (|CFloat|_|) =
        function
        | CBigInteger _ -> None
        | Constant other -> Some other

    let public isOne (Constant cst) = cst = 1
    let public isZero (Constant cst) = cst = 0
    let public isNegative (Constant cst) = cst < 0
    let public cabs (Constant cst) = Constant(abs cst)
    let public toInt (Constant cst) = int cst
    let public toDouble (Constant cst) = cst
    let public toBigInt (Constant cst) = bigint cst

    /// Apply the given mapping to the given constant.
    let inline public mapf ([<InlineIfLambda>] mapper: double -> double) (Constant cst) =
        Constant(mapper cst)

    /// Determine whether the two constants are equal to the given precision.  If `eps` is `None` then the
    /// comparison is made with a fixed femto-precision (`1e-15`).
    let inline public approximatelyEquals (Constant a) (Constant b) (eps: double voption) =
        Math.approximatelyEquals a b eps
