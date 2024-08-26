namespace Liyh.Kernel

module public rec Equation =
    open System.Collections.Generic
    open System
    open Liyh.Kernel
    open System.Runtime.CompilerServices
    open Liyh.Utils

    type public Variable = SumPow

    [<Struct>]
    type public EquationKind =
        | Equality
        | LesserThan
        | LesserOrEqualThan
        | GreaterThan
        | GreaterOrEqualThan

    [<Symbolic; Struct>]
    type public Equation =
        | Equation of kind: EquationKind * lhs: SumPow * rhs: SumPow

        interface ISymbolic with
            member this.ToSymbolic() = toSymbolic this
            member this.ToLatex() = Some(toLatex this)
            member this.ToLatexOrString() = toLatex this
            member this.Hash = hash this

    let private toLatex (Equation(kind, lhs, rhs)) =
        let kind =
            match kind with
            | Equality -> "="
            | LesserThan -> "<"
            | LesserOrEqualThan -> @"\leqslant"
            | GreaterThan -> ">"
            | GreaterOrEqualThan -> @"\geqslant"

        sprintf "%s %s %s" (toLatexValue lhs) kind (toLatexValue rhs)

    let private toSymbolic (Equation(kind, lhs, rhs)) =
        let kind =
            match kind with
            | Equality -> "Eq"
            | LesserThan -> "Ls"
            | LesserOrEqualThan -> "Lseq"
            | GreaterThan -> "Gr"
            | GreaterOrEqualThan -> "Greq"

        { atom = Identifier "Equation"
          attributes =
            [ ("kind", atom (Identifier kind))
              ("lhs", Symbolic.toSymbolic lhs)
              ("rhs", Symbolic.toSymbolic rhs) ] }

    let inline private getLHS (Equation(_, lhs, _)) = lhs
    let inline private getRHS (Equation(_, _, rhs)) = rhs
    let inline private getSides (Equation(_, lhs, rhs)) = lhs, rhs
    let inline private getKind (Equation(kind, _, _)) = kind

    [<RequireQualifiedAccess>]
    module public BasicOperations =

        /// Transform the equation (lhs = rhs) in the equivalent form (0 = rhs - lhs).
        let inline public leftZero (Equation(kind, lhs, rhs)) =
            Equation(kind, SumPow.Const Zero, rhs - lhs)

        /// Transform the equation (lhs = rhs) in the equivalent form (lhs - rhs = 0).
        let inline public rightZero (Equation(kind, lhs, rhs)) =
            Equation(kind, lhs - rhs, SumPow.Const Zero)

        /// Given an equation LHS(x₁, x₂, ..., xₙ) = RHS(x₁, x₂, ..., xₙ), return P(x₁, x₂, ..., xₙ) for P(x₁, x₂, ..., xₙ) = 0.
        let inline public equateToZero (Equation(_, lhs, rhs)) = lhs - rhs

        let inline private binOpBySumPow (op: SumPow -> SumPow -> SumPow) (Equation(kind, lhs, rhs)) (sp: SumPow) =
            Equation(kind, op lhs sp, op rhs sp)

        /// Adds `sp` to both sides of the equation.
        let public additionBySumPow = binOpBySumPow ( + )

        /// Adds `sp` to both sides of the equation.
        let public subtractionBySumPow = binOpBySumPow ( - )

    module public NumericEvaluation =
        open SumPow.NumericEvaluation

        /// Recursive version of the ITP (Interpolate Truncate and Project) method.
        /// See https://en.wikipedia.org/wiki/ITP_method.
        /// See https://dl.acm.org/doi/10.1145/3423597.
        let private ITP (a: double) (b: double) (ε: double) (κ1: double) (κ2: double) (n: int) (f: double -> double) =
            let n' = ceil (log ((b - a) / (2. * ε)) / log 2.)
            let nₘₐₓ = n' + double n

            let rec loop (a: double) (b: double) (ya: double) (yb: double) (k: double) =
                if (b - a <= 2. * ε) then (a + b) / 2. else

                // Calculating Parameters.

                let x' = (a + b) / 2.
                let r = ε * (2. ** (nₘₐₓ - k)) - (b - a) / 2.
                let δ = κ1 * ((b - a) ** κ2)

                // Interpolation.

                let xf = (yb * a - ya * b) / (yb - ya)

                // Truncation.

                let σ = (sign >> double) (x' - xf)
                let xt = if δ <= abs (x' - xf) then xf + σ * δ else x'

                // Projection.

                let xᵢₜₚ = if abs (xt - x') <= r then xt else x' - σ * r

                // Updating interval.

                let yᵢₜₚ = f xᵢₜₚ

                let a, b, ya, yb =
                    if   yᵢₜₚ > 0 then a, xᵢₜₚ, ya, yᵢₜₚ
                    elif yᵢₜₚ < 0 then xᵢₜₚ, b, yᵢₜₚ, yb
                    else               xᵢₜₚ, xᵢₜₚ, ya, yb

                loop a b ya yb (k + 1.)

            loop a b (f a) (f b) 0


