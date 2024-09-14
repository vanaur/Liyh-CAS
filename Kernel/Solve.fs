namespace Liyh.Kernel

#nowarn "3391"
#nowarn "25"
#nowarn "26"

module public Solve =
    open System
    open System.Numerics
    open Liyh.Utils
    open Liyh.Kernel
    open Liyh.Kernel.SumPow.PureConstantExpression
    open Liyh.Kernel.Equation
    open Liyh.Kernel.MultiLinearAlgebra
    open Liyh.Kernel.Polynomial.Factorization

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

    [<NoComparison; RequireQualifiedAccess>]
    type public SolutionKind =
        | Exact of SumPow                   // Liyh found a root algebraically.
        | Approximate of SumPow             // Liyh not found a root algebraically and returns a numerical root.
        | Unfound of Polynomial.Polynomial  // No roots were found for the polynomial indicated.

    /// The multiplicity of the solutions are not returned.
    let public trySolvePolynomialEquation (PolynomialEquation.PolyEq (kind, poly)) =
        // Equality

        let rec solve poly =
            match tryFactoring poly None with
            | FactoringResult.Univariate [ (poly', 1) ] when poly' = poly ->
                if Map.count poly.polynomial = 1 && not (Polynomial.Tools.isConstantPolynomial poly) then
                    // It is an equation of the form P(x) ≡ αxⁿ = 0, so x = 0.
                    Some [ SolutionKind.Exact (Const Zero) ]
                else
                    match Polynomial.Tools.totalDegree poly with
                    | 0 -> None // Not a solution, but a multiplicative factor.
                    | 1 ->
                        let ct = Polynomial.Tools.getConstantTerm poly
                        let lc = Polynomial.Tools.leadingCoeff poly

                        // It is an equation of the form P(x) ≡ αx + β = 0, so x = -β/α.
                        Some [ SolutionKind.Exact (Simplification.simplify -(ct / lc)) ]

                    | _ ->
                        // The polynomial has roots which cannot be isolated algebraically by Liyh,
                        // so we try numerical methods to find all the roots.
                        match Polynomial.NumericEvaluation.tryNumericUnivariatePolynomial poly with
                        | None -> Some [ SolutionKind.Unfound poly ]
                        | Some nup ->
                            // An accuracy of 0.00001 and a maximum number of iterations of 15 are "imposed".
                            // The user can specify this when calling a specifically numerical function.
                            match Polynomial.NumericEvaluation.findRoots nup 0.00001 15 with
                            | None ->
                                // This means that the underlying algorithm for finding roots has not converged, in
                                // other words the parameters provided here (precision and number of iterations) are
                                // not adapted to the polynomial being processed.
                                Some [ SolutionKind.Unfound poly ]

                            | Some nsols ->
                                let inline mapper (a: Complex) = Fun("Complex", [ Const a.Real; Const a.Imaginary ])
                                let nsols = Array.map mapper nsols

                                Some (List.map SolutionKind.Approximate (List.ofArray nsols))

            | FactoringResult.Univariate univc ->
                let sols = List.map (fst >> solve) univc |> List.choose id |> List.flatten
                if not (List.isEmpty sols) then Some sols else None

        match solve poly with
        | Some sols -> sols
        | None -> failwith "??" // this might not happen, the option is used to indicate whether a multiplicative factor
                                // exists in the equation and that it can be removed, which does not affect the result.

    /// Solve the given polynomial equation. The result is a list of tuples, each tuple indicating a root and its
    /// multiplicity. The roots can be either `Exact`, `Approximate` or `Unfound`.
    let inline public solvePolynomialEquationWithmultiplicity (peq: PolynomialEquation.PolyEq) =
           List.groupBy id (trySolvePolynomialEquation peq)
        |> List.map (fun (x, occ) -> x, List.length occ)

    /// Solve the given polynomial equation. The result is a list of root.
    /// The roots can be either `Exact`, `Approximate` or `Unfound`.
    let inline public solvePolynomialEquation (peq: PolynomialEquation.PolyEq) =
        List.distinct (trySolvePolynomialEquation peq)

    /// 
    let public trySolvePolynomialEquationSystem (PolynomialEquation.PolyEqSystem system as sys) =
        match PolynomialEquation.tryAsLinearEquationSystem sys with
        | Some lineqSys -> Some (trySolveLinearEquationSystem lineqSys)
        | None ->
            if not (List.forall (function PolynomialEquation.PolyEq (kind, _) -> kind = Equality) system) then None
            else
                let equations = List.map (function PolynomialEquation.PolyEq (_, polyeq) -> polyeq) system
                let gb = Polynomial.GroebnerBasis.computeGroebnerBasis equations // May timeout!

                // TODO: For some as yet unknown reason, the algorithm we have implemented does not work for all
                // inputs and loops ad infinitum... Pending a solution to the problem, we cannot decently continue
                // the implementation of this function for now. See commit 8fb6049.

                None

    module public NumericEvaluation =
        open SumPow.NumericEvaluation

        exception public InvalidEpsException of double

        // Numerical root finding algorithms implemented:
        //
        //  1. Newton's method:
        //      - great for speed
        //      - require the derivative (not a problem in a symbolic engine)
        //      - no guarantee of convergence
        //  2. Bisection method:
        //      - guarantee of convergence
        //      - very slow
        //  3. ITP method:
        //      - guarantee of convergence
        //      - good speed
        //  4. Steffensen method:
        //      - same convergence as Newton but not require the derivative
        //      - slower than Newton
        //      - no guarantee of convergence
        //  5. Illinois method:
        //      - improved regula falsi method
        //      - good speed
        //      - guarantee of convergence
        //

        [<Struct; NoEquality; NoComparison>]
        type public RealInterval =
            { a: double
              b: double }

        /// Checks if the interval is empty.
        let inline private isEmptyInterval { a = a; b = b } = b < a

        [<NoComparison; NoEquality>]
        type public RootFinder =
            | ITP           of {| interval: RealInterval; eps: double; κ1: double; κ2: double; n: int; f: double -> double |}
            | ITP'          of {| interval: RealInterval; eps: double; f: double -> double |}
            | Bisection     of {| interval: RealInterval; eps: double; f: double -> double |}
            | Illinois      of {| interval: RealInterval; eps: double; f: double -> double |}
            | Steffensen    of {| initialGuess: double; eps: double; maxIter: int option; f: double -> double |}
            | NewtonRaphson of {| initialGuess: double; eps: double; maxIter: int option; f: double -> double; f': double -> double |}

        [<NoComparison; NoEquality; Struct; RequireQualifiedAccess>]
        type public RootFinderResult =
            | Root of double    // The root found
            | NoRoot            // The interval contains no root
            | Failed            // The algorithm didn't converged

        /// Assuming the function is continuous, check whether the function has at least one root in the interval `[a, b]`.
        let inline private containsRoot { a = a; b = b } (eps: double) (f: double -> double) =
            if isEmptyInterval { a = a; b = b } then false else
            let t = (f a) * (f b) in t < 0 || Math.approximatelyEquals t 0 (ValueSome eps)

        /// Recursive version of the ITP (Interpolate Truncate and Project) method.
        /// See https://en.wikipedia.org/wiki/ITP_method.
        /// See https://dl.acm.org/doi/10.1145/3423597.
        let private ITP { a = a; b = b } (ε: double) (κ1: double) (κ2: double) (n: int) (f: double -> double) =
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

        /// Recursive version of the Steffensen's method.
        /// See https://en.wikipedia.org/wiki/Steffensen%27s_method.
        let private steffensen (initialGuess: double) (eps: double) (maxIter: int option) (f: double -> double) =

            let rec loop x k =
                let fx = f x

                if abs fx <= eps then x
                else loop (x - (pown fx 2) / (fx - f (x - fx))) (k + 1)

            loop initialGuess 0

        /// Recursive version of the secant method.
        /// See https://en.wikipedia.org/wiki/Secant_method.
        let private bisection { a = a; b = b } (eps: double) (f: double -> double) =

            let rec loop a b x k =
                let fx = f x

                if abs fx <= eps then x else

                let a, b = if f a * fx > 0 then x, b else a, x
                loop a b ((a + b) / 2.) (k + 1)

            loop a b ((a + b) / 2.) 0

        /// Recursive version of the Illinois method.
        /// See https://en.wikipedia.org/wiki/Regula_falsi#The_Illinois_algorithm.
        let private illinois { a = a; b = b } (eps: double) (f: double -> double) =

            let rec loop a b fa fb k =
                let x = (a + b) / 2.
                let fx = f x

                if abs fx <= eps then x else

                let c = b - fb * (b - a) / (fb - fa)
                let fc = f c
                
                let a, fa = if fb * fc < 0. then b, fb else a, (fa / 2.)
                let b, fb = c, fc

                loop a b fa fb (k + 1)

            loop a b (f a) (f b) 0

        /// Recursive version of the Newton's method.
        /// See https://en.wikipedia.org/wiki/Newton%27s_method.
        let private newtonRaphson (initialGuess: double) (eps: double) (maxIter: int option) (f: double -> double) (f': double -> double) =

            let rec loop x0 k =
                let fx = f x0

                if abs fx <= eps then x0 else

                let x1 = x0 - fx / f' x0
                loop x1 (k + 1)

            loop initialGuess 0

        /// Use a given method and its parameters to find an approximated real root.
        let public findRoot (method: RootFinder) =
            match method with
            | ITP rf -> ITP rf.interval rf.eps rf.κ1 rf.κ2 rf.n rf.f
            | ITP' rf -> ITP rf.interval rf.eps 0.1 (0.98 * (1. + (1. + sqrt 5.) / 2.)) 2 rf.f
            | Bisection rf -> bisection rf.interval rf.eps rf.f
            | Illinois rf -> illinois rf.interval rf.eps rf.f
            | Steffensen rf -> steffensen rf.initialGuess rf.eps rf.maxIter rf.f
            | NewtonRaphson rf -> newtonRaphson rf.initialGuess rf.eps rf.maxIter rf.f rf.f'

        /// The default root finder for Liyh. The function takes the bounds between which to try to deduce
        /// a root, as well as the univariate SumPow expression function of the given variable to be tested.
        /// The numerical method used is the ITP method.
        let public defaultRootFinder (interval: RealInterval) (eps: double) (expr: SumPow) (variable: string) =
            if eps <= 0 then
                raise (InvalidEpsException eps)

            let fn = (makef1 expr variable)
            if not (containsRoot interval eps fn) then RootFinderResult.NoRoot else

            let rnd = digitCountBigInt (bigint (1. / (eps - truncate eps))) - 1
            let rnd = if rnd < 15 then rnd else 15

            let root = findRoot (ITP' {| interval = interval; eps = eps; f = fn |})
            RootFinderResult.Root (Math.Round(root, rnd))


// Inéqualitées https://tutorial.math.lamar.edu/classes/alg/solvepolyinequalities.aspx
