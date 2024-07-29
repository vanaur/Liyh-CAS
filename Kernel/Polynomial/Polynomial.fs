namespace Liyh.Kernel.Polynomial

[<AutoOpen>]
module rec Polynomial =
    open Liyh.Utils
    open System.Linq
    open Liyh.Kernel.SumProd

    /// Adds `x` to the end of the list `xs`.
    let inline private ( @@ ) (xs: 'a list) (x: 'a) = xs @ [ x ]

    /// If the given list matches a polynomial in the variable `x` (at least) then builds a polynomial.
    let private tryMakeUnivariatePolynomial (variable: SumProd) (xs: SumProd list) =

        // Checks whether the two given expressions have the same base.
        let hasSameBase = function
            | Pow (a, _), Pow (b, _) -> a = b
            | a, Pow (b, _) -> a = b
            | Pow (a, _), b -> a = b
            | a, b -> a = b

        // Returns the power of the given expression.
        let getPow pvar = function
            | Pow (_, Integer n) -> int n
            | x when x = pvar -> 1
            | _ -> 0

        /// Returns the power's base of the given expression.
        let getBase = function
            | Pow (a, _) -> a
            | a -> a

        /// Checks whether the given term is a valid term for a monomial.
        let hasExpectedExponent pvar = function
            | Pow (_, Integer n) when n >= 0I -> true
            | x when x = pvar -> true
            | _ -> false

        /// Returns the various ingredients to construct a polynomial. Returns `None` if the expression is not
        /// a polynomial, otherwise returns the variable (or variable expression) of the polynomial and the monomials.
        let rec inner = function
            | pvar, acc, [] -> Some (pvar, acc)
            | pvar, acc, CteTimesSPUsingVars [ variable ] (coeff, term) :: xs ->

                let pvar = if pvar <> Null then pvar else getBase term

                if not (hasExpectedExponent pvar term) then None
                else
                    let m = Univariate.monomial coeff (getPow pvar term)

                    if List.isEmpty acc || hasSameBase (pvar, term)
                    then inner (pvar, acc @@ m, xs) else None

            | pvar, acc, ConstWithRespectTo [ variable ] x0 :: xs ->
                inner (pvar, acc @@ Univariate.monomial x0 0, xs)
            | _ -> None

        match inner (Null, [], xs) with
        | Some (pvar, monomials) -> Some (Univariate.Polynomial(pvar, monomials))
        | None -> None

    /// Consider a univariate polynomial in the variable `x`. If it is not the variable `x` that is directly used as
    /// a variable, but an expression in `x`, then use that expression as the variable of the polynomial.
    /// For example `3Cos[x]² + 7Cos[x] + 2` will be recognised as a polynomial in the general variable `Cos[x]`
    /// and the internal variable `x`.
    let public (|UnivariatePolynomial|_|) (variable: SumProd) = function
        | Sum xs -> tryMakeUnivariatePolynomial variable xs
        | x -> tryMakeUnivariatePolynomial variable [ x ]
