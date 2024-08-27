namespace Liyh.Kernel

#nowarn "25"

module public rec Equation =
    open Liyh.Kernel
    open Liyh.Utils

    exception public NotSymbolicEquationException of Symbol

    [<Struct; NoComparison>]
    type public EquationKind =
        | Equality
        | LesserThan
        | LesserOrEqualThan
        | GreaterThan
        | GreaterOrEqualThan

    [<Symbolic; Struct; NoComparison>]
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

    /// Convert from a symbolic representation to the representation of equation in SumPow.
    let public fromSymbolic (symbolic: Symbol) =

        let getKind =
            function
            | "Eq" -> Equality
            | "Ls" -> LesserThan
            | "Lseq" -> LesserOrEqualThan
            | "Gr" -> GreaterThan
            | "Greq" -> GreaterOrEqualThan
            | _ -> raise (NotSymbolicEquationException symbolic)

        match symbolic.atom with
        | Identifier "Equation" ->
            if List.length symbolic.attributes <> 3 then raise (NotSymbolicEquationException symbolic)
            let [ kind; lhs; rhs ] = getArgumentsByName [ "kind"; "lhs"; "rhs" ] symbolic

            match kind with
            | { atom = Identifier kind } -> Equation (getKind kind, toSumPow lhs, toSumPow rhs)
            | _ -> raise (NotSymbolicEquationException symbolic)

        | _ -> raise (NotSymbolicEquationException symbolic)

    [<RequireQualifiedAccess>]
    module public BasicOperations =

        /// Transform the equation (lhs = rhs) in the equivalent form (0 = rhs - lhs).
        let inline public leftZero (Equation(kind, lhs, rhs)) =
            Equation(kind, SumPow.Const Zero, rhs - lhs)

        /// Transform the equation (lhs = rhs) in the equivalent form (lhs - rhs = 0).
        let inline public rightZero (Equation(kind, lhs, rhs)) =
            Equation(kind, lhs - rhs, SumPow.Const Zero)

        /// Given an equation LHS(x₁, x₂, ..., xₙ) = RHS(x₁, x₂, ..., xₙ), return P(x₁, x₂, ..., xₙ) for P(x₁, x₂, ..., xₙ) = 0.
        let inline public equateToZero (Equation(_, lhs, rhs)) =
            lhs - rhs

        let inline private binOpBySumPow (op: SumPow -> SumPow -> SumPow) (Equation(kind, lhs, rhs)) (sp: SumPow) =
            Equation(kind, op lhs sp, op rhs sp)

        /// Adds `sp` to both sides of the equation.
        let public additionBySumPow =
            binOpBySumPow ( + )

        /// Adds `sp` to both sides of the equation.
        let public subtractionBySumPow =
            binOpBySumPow ( - )

    module public NumericEvaluation =
        open SumPow.NumericEvaluation

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

        [<NoComparison; NoEquality>]
        type public RootFinder =
            | ITP           of {| a: double; b: double; eps: double; κ1: double; κ2: double; n: int; f: double -> double |}
            | ITP'          of {| a: double; b: double; eps: double; f: double -> double |}
            | Bisection     of {| a: double; b: double; eps: double; maxIter: int option; f: double -> double |}
            | Illinois      of {| a: double; b: double; eps: double; maxIter: int option; f: double -> double |}
            | Steffensen    of {| initialGuess: double; eps: double; maxIter: int option; f: double -> double |}
            | NewtonRaphson of {| initialGuess: double; eps: double; maxIter: int option; f: double -> double; f': double -> double |}

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

        /// Recursive version of the Steffensen's method.
        /// See https://en.wikipedia.org/wiki/Steffensen%27s_method.
        let private steffensen (initialGuess: double) (eps: double) (maxIter: int option) (f: double -> double) =

            let rec loop x k =
                let fx = f x

                if abs fx <= eps
                    || Math.approximatelyEquals fx 0 (ValueSome eps)
                    || Option.defaultValue false (Option.map (( >= ) k) maxIter)
                then x
                else loop (x - (pown fx 2) / (fx - f (x - fx))) (k + 1)

            loop initialGuess 0

        /// Recursive version of the secant method.
        /// See https://en.wikipedia.org/wiki/Secant_method.
        let private bisection (a: double) (b: double) (eps: double) (maxIter: int option) (f: double -> double) =

            let rec loop a b x k =
                let fx = f x

                if abs fx <= eps
                    || Math.approximatelyEquals fx 0 (ValueSome eps)
                    || Option.defaultValue false (Option.map (( >= ) k) maxIter)
                then x
                else
                    let a, b = if f a * fx > 0 then x, b else a, x
                    loop a b ((a + b) / 2.) (k + 1)

            loop a b ((a + b) / 2.) 0

        /// Recursive version of the Illinois method.
        /// See https://en.wikipedia.org/wiki/Regula_falsi#The_Illinois_algorithm.
        let private illinois (a: double) (b: double) (eps: double) (maxIter: int option) (f: double -> double) =

            let rec loop a b fa fb k =
                let x = (a + b) / 2.
                let fx = f x

                if abs fx <= eps
                    || Math.approximatelyEquals fx 0 (ValueSome eps)
                    || Option.defaultValue false (Option.map (( >= ) k) maxIter)
                then x
                else
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

                if abs fx <= eps
                    || Math.approximatelyEquals fx 0 (ValueSome eps)
                    || Option.defaultValue false (Option.map (( >= ) k) maxIter)
                then x0
                else
                    let x1 = x0 - fx / f' x0
                    loop x1 (k + 1)

            loop initialGuess 0

        /// Use a given method and its parameters to find an approximated real root.
        let public findRoot (method: RootFinder) =
            match method with
            | ITP rf -> ITP rf.a rf.b rf.eps rf.κ1 rf.κ2 rf.n rf.f
            | ITP' rf -> ITP rf.a rf.b rf.eps 0.1 (0.98 * (1. + (1. + sqrt 5.) / 2.)) 2 rf.f
            | Bisection rf -> bisection rf.a rf.b rf.eps rf.maxIter rf.f
            | Illinois rf -> illinois rf.a rf.b rf.eps rf.maxIter rf.f
            | Steffensen rf -> steffensen rf.initialGuess rf.eps rf.maxIter rf.f
            | NewtonRaphson rf -> newtonRaphson rf.initialGuess rf.eps rf.maxIter rf.f rf.f'

        /// The default root finder for Liyh. The function takes the bounds between which to try to deduce
        /// a root, as well as the function to be tested.
        let public defaultRootFinder' (a: double) (b: double) (f: double -> double) =
            let a, b = min a b, max a b
            findRoot (Illinois {| a = a; b = b; eps = 0.001; maxIter = Some 25; f = f |})

        /// The default root finder for Liyh. The function takes the bounds between which to try to deduce
        /// a root, as well as the SumPow expression function of the given variable to be tested.
        let public defaultRootFinder (a: double) (b: double) (expr: SumPow) (variable: string) =
            defaultRootFinder' a b (makef1 expr variable)

