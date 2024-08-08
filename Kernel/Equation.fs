namespace Liyh.Kernel

module public rec Equation =
    open System.Collections.Generic
    open System
    open Liyh.Kernel
    open System.Runtime.CompilerServices
    open Liyh.Kernel.Constant
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
        open System.Numerics

        let private brent (a: double) (b: double) (f: SumPow) (variable: Variable) = 0
        // il faut faire un module poue les fonctions...

