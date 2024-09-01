namespace Liyh.Kernel

#nowarn "25"

module public Solve =
    open System
    open Liyh.Utils
    open Liyh.Kernel
    open Liyh.Kernel.SumPow.PureConstantExpression
    open Liyh.Kernel.Equation
    open Liyh.Kernel.MultiLinearAlgebra

    /// If the linear equation is of the diophantine type (only integer solutions are of interest and/or possible) and
    /// its coefficients are integers, then return the general solution of the equation.
    /// 
    /// For there to be a solution, the equation must be of the form
    /// 
    ///     a₁x₁ + a₂x₂ + ... aₙxₙ = b
    /// 
    /// where each `aᵢ` is an integer and `b` is an integer too such that `GCD({aᵢ}) = d | b`. If `d` does not divide `b`,
    /// then there is no solution in the integers; but `b` (the LinEq constant) does not need to be syntactically integer.
    /// 
    /// The function return consists of a list of tuples `(variable, solution)` such that each solution can present
    /// some constant parameters (the name of which is specified in the function entry).
    let public trySolveLinearDiophantineEquation (LinearEquation.LinEq(kind, (map, constant))) (parameterName: string) =
        if kind <> Equality then None else // don't apply for inequalities

        let equation = Map.toArray map

        if not (Array.forall (snd >> Misc.isPureConstInteger) equation) then None else

        let iequation = Array.map (function (var, PureConstantExpressionInteger factor) -> var, bigint factor) equation
        let variables, coefficients = Array.unzip iequation
        let gcd = Array.fold bigintGCD 0I coefficients |> fromBigInt |> Const

        // The algorithm to find the solution is based on formatting the equation as a matrix problem with a
        // single column of coefficients, applying the Hermite reduction to this column and using the unimodular
        // matrix of operations to extract the result by columns.

        let columnMatrix = Array2D.init (Array.length coefficients) 1 (fun i _ -> coefficients.[i])
        let _, U = VectorSpaceUtility.hermiteNormalForm' columnMatrix

        let inline initializer (column: bigint[]) (i: int) =
              (if i = 0 then -(constant / gcd) else Name(sprintf "%s_{%d}" parameterName i))
            * (Const(fromBigInt column.[i]))

        let result =
            [ for col in 0 .. Array2D.length2 U - 1 do
                    let column = U.[*, col]
                    let sol = Array.init (Array.length column) (initializer column)

                    variables.[col], (Simplification.simplify (Array.reduce ( + ) sol)) ]

        Some result


