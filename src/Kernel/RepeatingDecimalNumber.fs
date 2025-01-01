namespace Liyh.Kernel

(* This module can be used to represent rational numbers with periodic decimal places using either the fraction data,
   the abbreviated data or the parameters essential to the representation of the number. A number with periodic decimals
   can be converted into a fraction (and an additive term). To do this, the algorithm uses the convergence of the
   infinie sum representation of the number (in O(1) time). *)

[<RequireQualifiedAccess>]
module rec RepeatingDecimalNumber =
    open Liyh.Utils
    open FParsec

    /// A data type representing a fraction for temporary use in calculations and to interface more easily.
    [<Struct>]
    type public TemporaryFraction =
        | TFraction of numerator: int * denominator: int

        override this.ToString() =
            match this with
            | TFraction(num, den) -> sprintf "%d/%d" num den

    let public fromString (str: string) =
        let pintStr = many1 digit |>> System.String.Concat

        let inner = function
            | b, None, None -> RepeatingDecimalNumber(decimal b, 0, 0, 0)
            | b, Some c, Some d ->
                let a = decimal (sprintf "%s.%s" b c)
                let k = String.length c
                let αβ'γ = int d
                let r = String.length d
                RepeatingDecimalNumber(a, k, αβ'γ, r)
            | b, None, Some d ->
                let a = decimal (sprintf "%s." b)
                let k = 0
                let αβ'γ = int d
                let r = String.length d
                RepeatingDecimalNumber(decimal a, k, αβ'γ, r)
            | b, Some c, None -> RepeatingDecimalNumber(decimal (sprintf "%s.%s" b c), 0, 0, 0)

        let miniParser =
            pipe4 pintStr (pchar '.') (opt pintStr) (opt (between (pchar '(') (pchar ')') pintStr)) (fun b _ c d ->
                inner (b, c, d))

        match runParserOnString miniParser () null str with
        | Success(result, _, _) -> result
        | Failure(msg, _, _) -> failwith msg

    /// Number of the form `a + 0.00...0αβ...γ` where `a` is the additive term, `0.00...0` are the `k` zeros
    /// before the repeating decimals `αβ...γ`, of which there are `r`. For example, let's take `0.0(675)`.
    /// We have: `a=0`, `k=1`, `αβ...γ=675` and `r=3`.
    [<Struct>]
    type public RepeatingDecimalNumber(a: decimal, k: int, αβ'γ: int, r: int) =

        /// Displays the number with repeated decimal in parenthesis notation.
        override __.ToString() =
            let aStr = if a = 0m then "" else sprintf "%g + " a
            let kStr = sprintf "0.%s" (System.String('0', k))
            sprintf "%s%s(%s%d)" aStr kStr (System.String('0', r - digitCount αβ'γ)) αβ'γ

        /// Apply numerically the formula `a + αβ...γ/(10^(k+r) - 10^k)`.
        member public __.Approximate = a + decimal αβ'γ / decimal (pown 10 (k + r) - pown 10 k)

        /// Gets the representation as a fraction.
        member public __.GetFraction =
            let fixSign (p, q) = if sign q > 0 then (p, q) else (-p, -q)
            let num, den = αβ'γ, (pown 10 (k + r) - pown 10 k)

            if den = 0 then
                raise (System.DivideByZeroException())

            let g = intGCD den num
            let frac = fixSign (num / g, den / g)
            (a, TFraction frac)

        /// Gets the period of the repeating decimal number.
        member public __.GetPeriod = r

// NOTE: In general, converting a fraction into `RepeatingDecimalNumber` is a computationally
// complicated problem. At least I think so.
