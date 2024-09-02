namespace Liyh.Kernel

#nowarn "25"
#nowarn "26"

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

    /// A linear system may behave in three possible ways.
    [<Struct; NoEquality; NoComparison; RequireQualifiedAccess>]
    type public LinearSystemSolutionKind =
        | UniqueSolution        // The system has a unique solution.
        | NoSolution            // The system has no solution.
        | InfiniteSolutions     // The system has infinitely many solutions.

        override this.ToString() =
            match this with
            | InfiniteSolutions -> "the linear system has infinitely many solutions"
            | UniqueSolution -> "the linear system has a unique solution"
            | NoSolution -> "the linear system has no solution"

    /// Analyse the general behaviour of the solution system and conclude what kind of solution has been found.
    /// See https://en.wikipedia.org/wiki/System_of_linear_equations#General_behavior.
    let private identifieLinearSystemSolutionKind (variables: string array) (solution: array<SumPow * SumPow>) =
        let nEquations = Array.length solution
        let nVariables = Array.length variables

        if nEquations = nVariables then LinearSystemSolutionKind.UniqueSolution
        elif nEquations < nVariables then LinearSystemSolutionKind.InfiniteSolutions
        else LinearSystemSolutionKind.NoSolution

    /// Solve the system of linear equation and indicates the kind of solution found. If the function returns ‘None’
    /// this indicates that the system contains inequalities, which is not currently managed. The function is based
    /// on Gauss elimination to determine the system's unique solution.
    /// See https://en.wikipedia.org/wiki/System_of_linear_equations#Row_reduction.
    let public trySolveLinearEquationSystem (LinearEquation.LinEqSystem(system, variables)) =

        /// The system of equations may not contain all the variables given, so we list those that are not present.
        let unusedVariables =
            system
            |> List.collect (function LinearEquation.LinEq(_, (map, _)) -> (Map.keys >> List.ofSeq) map)
            |> Set.ofList
            |> Set.difference (Set.ofList variables)
            |> Set.toList
        
        /// Lists the variables in the system of equations.
        let usedVariables = List.except unusedVariables variables

        /// "Handle Missing Variables" when the linear equation miss some variables.
        let inline hmv (map: Map<string, SumPow>) =
            let rec loop result =
                function
                | [] -> result
                | v :: vs -> loop (Map.addOrUpdate v (Const Zero) result id) vs
            loop map usedVariables

        /// Builds the matrix (in list form) and the vector of constants from the system.
        let rec loop result aug =
            function
            | [] -> Option.map (flip tuple2 aug) result
            | LinearEquation.LinEq(Equality, (map, constant)) :: xs ->
                let t = Array.map snd (Map.toArray (hmv map))
                loop (Option.map (fun r -> t :: r) result) (-constant :: aug) xs
            | _ -> None

        // The ‘Map’ type is such that the variables will be given in the correct order for each equation,
        // whatever the initial encoding order. All we need to do is order the list of variables given
        // to match them to the calculated solutions.
        let variables = Array.sort (Array.ofList usedVariables)

        /// We put the system into staggered form using Gaussian elimination, and this gives us the result: each
        /// line corresponds to a simplified equation which potentially gives the solution, depending on the system.
        let inline binder (lst, aug) =
            let matrixForm = Matrix.fromArray (Array.ofList lst)
            let augVector = Vector.fromSeq aug
            let augM = VectorSpaceUtility.augmentedMatrix matrixForm augVector
            let rowEchelonForm = VectorSpaceUtility.gaussianElimination augM

            let rows = Matrix.getRows rowEchelonForm
            let solc = Array.map Array.last rows
            let rows = Array.map (fun (row: _[]) -> row.[.. Array.length row - 2]) rows

            let result = 
                Array.map2 (fun lhs rhs -> 

                    let lhs =
                        Array.mapi (fun j c -> c * Name variables.[j]) lhs
                        |> Array.reduce ( + )
                        |> Simplification.simplify

                    in lhs, rhs) rows solc

            // We filter out trivial solutions (like 0 = 0 for example).
            let filteredResult = Array.filter (uncurry ( <> )) result
            Some (identifieLinearSystemSolutionKind variables filteredResult, filteredResult)

        Option.bind binder (loop (Some List.empty) List.empty system)
