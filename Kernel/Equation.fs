namespace Liyh.Kernel

#nowarn "25"

module public rec Equation =
    open Liyh.Kernel
    open Liyh.Kernel.TrueVariable
    open Liyh.Utils
    open PureConstantExpression

    exception public NotSymbolicEquationException of Symbol
    exception public UnboundVariableException of string

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

        /// Updates the meaning of inequality given a multiplicative factor.
        /// For example, `-3x < 1` <=> `x > -1/3`.
        let inline public updateKind (kind: EquationKind) (factor: SumPow) =
            if kind = Equality then
                Equality
            else
                match factor with
                | Negative _ ->
                    match kind with
                    | LesserThan -> GreaterThan
                    | LesserOrEqualThan -> GreaterOrEqualThan
                    | GreaterThan -> LesserThan
                    | GreaterOrEqualThan -> LesserOrEqualThan
                    | Equality -> failwith "??" // may not happen
                | _ -> kind

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

    /// The simpliest equations to handle. An equation of the form a₁x₁ + ... + aₙxₙ + b = 0 where {xᵢ} are variables
    /// and {b; aᵢ} are coefficients is said to be a linear equation. See https://en.wikipedia.org/wiki/Linear_equation.
    [<RequireQualifiedAccess>]
    module public LinearEquation =

        /// A linear equation is represented as a variable/coefficient dictionary and a constant term.
        [<NoEquality; NoComparison>]
        type public LinEq =
            | LinEq of EquationKind * (Map<string, SumPow> * SumPow)

        /// Try to match a linear equation from the given equation.
        let public lineq (Equation(kind, lhs, rhs)) (variables: string list) =

            /// The predicate matches only variables of the form `Name(string)`
            /// for `string` contained in the list of variables.
            let isvar = function | Name name when List.contains name variables -> true | _ -> false

            let inline update result constant =
                function

                // Term of a sum of the form 1x₁¹ or equally just x₁.

                | Name name as x ->
                    match List.tryFind (( = ) name) variables with
                    | None -> Some (result, (x + constant))
                    | Some var -> Some ((Map.addOrUpdate var (Const One) result (( + ) 1)), constant)

                // Term of a sum of the form ax₁¹ or equally just ax₁ where a is a constant factor.

                | ProdWithKeep isvar (var, coeff, n) ->
                    if n <> 1 then None else

                    let coeff = Misc.prodToSumPow coeff
                    let (Name var) = List.exactlyOne var

                    Some ((Map.addOrUpdate var coeff result (( + ) coeff)), constant)

                // Term of a sum of the form b, where b is a constant.

                | x when not (containsVariables x variables) -> Some (result, (x + constant))
                | _ -> None

            match Simplification.expandAndSimplify (lhs - rhs) with
            | SimplifiedSum.SumList sl -> // This pattern also accepts sums of 1 element.

                let rec loop result constant =
                    function
                    | [] -> if Map.isEmpty result then None else Some (result, constant)
                    | x :: xs -> Option.bind (fun (r, c) -> loop r c xs) (update result constant x)

                Option.map (fun res -> LinEq(kind, res)) (loop Map.empty (Const Zero) sl)

            | _ -> None

        /// Isolates the specified variable from the given linear equation. The function also returns the resulting
        /// equality or inequality if there is a change in the isolation process.
        let public isolate (variable: string) (LinEq (kind, (lin, constant))) =
            match Map.tryFind variable lin with
            | None -> raise (UnboundVariableException variable)
            | Some cv ->
                let result =
                    if Map.count lin = 1 then Const Zero
                    else Map.toArray lin
                      |> Array.filter (fst >> ( <> ) variable)
                      |> Array.map (fun a -> (snd a / cv) * Name (fst a))
                      |> Array.reduce ( + )

                -Simplification.simplify (result + constant / cv), BasicOperations.updateKind kind cv

        /// Returns all the "solutions" of the linear equation, isolating each variable.
        let public isolateAll (LinEq (_, (lin, _)) as lineq) =
            List.map (fun (v, _) -> v, isolate v lineq) (Map.toList lin)

        /// Check whether the given linear equation has integer solutions.
        let public hasIntegerSolutions (LinEq (kind, (map, constant))) =
            if kind <> Equality then false else // don't apply for inequalities

            let equation = Map.toList map

            if not (Misc.isPureConstInteger constant) &&
               not (List.forall (snd >> Misc.isPureConstInteger) equation) then false else

            let equation = List.map (function (var, PureConstantExpressionInteger factor) -> var, factor) equation
            let (PureConstantExpressionInteger b) = -constant
            let d = List.fold (fun acc a -> intGCD acc (snd a)) 0 equation

            b % d = 0

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

