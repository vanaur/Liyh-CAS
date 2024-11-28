namespace Liyh.Kernel

#nowarn "25"

module public rec Equation =
    open System.Collections.Generic
    open TrueVariable
    open Liyh.Utils
    open MathRender

    exception public NotSymbolicEquationException of Symbol
    exception public UnboundVariableException of string
    exception public NotEqualityException of Equation

    [<Struct; NoComparison>]
    type public EquationKind =
        | Equality
        | LesserThan
        | LesserOrEqualThan
        | GreaterThan
        | GreaterOrEqualThan

    let private equationKindToMathRender =
        function
        | Equality -> MathRenderHelper.symbol "="
        | LesserThan -> MathRenderHelper.le
        | LesserOrEqualThan -> MathRenderHelper.leq
        | GreaterThan -> MathRenderHelper.ge
        | GreaterOrEqualThan -> MathRenderHelper.geq

    [<Symbolic; Struct; NoComparison>]
    type public Equation =
        | Equation of kind: EquationKind * lhs: SumPow * rhs: SumPow

        interface ISymbolic with
            member this.ToSymbolic() = toSymbolic this
            member this.ToMathRender() = Some(toMathRender this)
            member this.ToMathRenderOrString() = Choice1Of2 (toMathRender this)
            member this.Hash = hash this

    let private toMathRender (Equation(kind, lhs, rhs)) =
        toMathRenderValue lhs ++ (equationKindToMathRender kind) ++ toMathRenderValue rhs

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

    /// Check whether the given point is a solution to the equation (does not apply for inequalities). 
    let public isSolution (point: Dictionary<string, SumPow>) (Equation (kind, lhs, rhs) as eq) =
        if kind <> Equality then
            raise (NotEqualityException eq)

        Subst.manySubstVar point (lhs - rhs) == Const Zero

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

    [<Symbolic; Struct; NoComparison>]
    type public EquationSystem =
        | EquationSystem of Equation list

        interface ISymbolic with
            member this.ToSymbolic() = toSymbolic' this
            member this.ToMathRender() = Some(toMathRender' this)
            member this.ToMathRenderOrString() = Choice1Of2 (toMathRender' this)
            member this.Hash = hash this

    let private toSymbolic' (EquationSystem sys) =
        { atom = Identifier "EquationSystem"
          attributes = List.map (fun x -> null, toSymbolic x) sys }

    let private toMathRender' (EquationSystem sys) =
        failwith "todo: implement *cases* in `MathRender`"

        // let inline innerLatex (Equation(kind, lhs, rhs)) =
        //     sprintf "%s &%s %s" (toLatexValue lhs) (equationKindToLatex kind) (toLatexValue rhs)
        // sprintf @"\begin{cases}%s\end{cases}" (System.String.Join(@"\\", (List.map innerLatex sys)))

    /// The simpliest equations to handle. An equation of the form a₁x₁ + ... + aₙxₙ + b = 0 where {xᵢ} are variables
    /// and {b; aᵢ} are coefficients is said to be a linear equation. See https://en.wikipedia.org/wiki/Linear_equation.
    [<RequireQualifiedAccess>]
    module public LinearEquation =

        /// A linear equation is represented as a variable/coefficient dictionary and a constant term.
        [<NoEquality; NoComparison>]
        type public LinEq =
            | LinEq of EquationKind * (Map<string, SumPow> * SumPow)

        /// A system of linear equations is represented as a list of linear equations and the list of variables.
        [<NoEquality; NoComparison>]
        type public LinEqSystem =
            | LinEqSystem of LinEq list * string list

        /// Return the list of variables of the given linear equation.
        let public getVariables (LinEq (_, (lin, _))) =
            Map.keys lin

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

        /// Try to match a system of linear equations from the given system of equations.
        let public lineqSystem (EquationSystem system) (variables: string list) =

            let rec loop result =
                function
                | [] -> result
                | x :: xs ->
                    Option.bind
                        (fun r -> loop (Option.map (fun res -> r :: res) result) xs)
                        (lineq x variables)

            Option.map (flip tuple2 variables >> LinEqSystem) (loop (Some List.empty) system)

//        /// Check whether the given linear equation has integer solutions.
//        let public hasIntegerSolutions (LinEq (kind, (map, constant))) =
//            if kind <> Equality then false else // don't apply for inequalities
//
//            let equation = Map.toList map
//
//            if not (Misc.isPureConstInteger constant) &&
//               not (List.forall (snd >> Misc.isPureConstInteger) equation) then false else
//
//            let equation = List.map (function (var, PureConstantExpressionInteger factor) -> var, factor) equation
//            let (PureConstantExpressionInteger b) = -constant
//            let d = List.fold (fun acc a -> intGCD acc (snd a)) 0 equation
//
//            b % d = 0

    [<RequireQualifiedAccess>]
    module public PolynomialEquation =

        exception public NotALinearEquationException of PolyEq

        /// A polynomial equation is represented using the associated representation.
        [<NoEquality; NoComparison>]
        type public PolyEq =
            | PolyEq of EquationKind * Polynomial.Polynomial

        /// A system of polynomial equations is represented as a list of polynomial equations.
        [<NoEquality; NoComparison>]
        type public PolyEqSystem =
            | PolyEqSystem of PolyEq list 

        /// Try to match a polynomial equation from the given equation.
        let public polyeq (Equation(kind, lhs, rhs)) (variables: string list option) (excludedVariables: string list) =
            let result =
                match Option.map (List.map Name) variables with
                | Some variables -> Polynomial.Pattern.tryAsMultivariatePolynomial variables excludedVariables (lhs - rhs)
                | None -> Polynomial.Pattern.tryAsGeneralPolynomial excludedVariables (lhs - rhs)

            Option.bind (fun (p, rest) -> if Option.isNone rest then Some (PolyEq (kind, p)) else None) result

        /// Try to match a system of polynomial equations from the given system of equations.
        let public polyeqSystem (EquationSystem system) (variables: string list option) (excludedVariables: string list) =

            let rec loop result =
                function
                | [] -> result
                | x :: xs ->
                    Option.bind
                        (fun r -> loop (Option.map (fun res -> r :: res) result) xs)
                        (polyeq x variables excludedVariables)

            Option.map PolyEqSystem (loop (Some List.empty) system)

        /// Check whether the polynomial equation reduces to a linear equation.
        let public isLinearEquation (PolyEq (_, { polynomial = polynomial })) =
            Seq.forall
                (function Polynomial.MonomialDegree deg -> List.forall (fun d -> d = 0 || d = 1) deg)
                (Map.keys polynomial)

        /// Check whether the system of polynomial equations reduces to a system of linear equations.
        let public isLinearEquationSystem (PolyEqSystem sys) =
            List.forall isLinearEquation sys

        [<Struct; RequireQualifiedAccess>]
        type public PolyEqAsLinEqResult =
            | NotLineq
            | NotNamedVariables
            | Lineq of LinearEquation.LinEq

        /// If the given polynomial equation is a linear equation, then convert it to a linear equation representation.
        let public tryAsLinearEquation (PolyEq (kind, polynomial) as polyeq) =
            if not (isLinearEquation polyeq) then
                PolyEqAsLinEqResult.NotLineq
            else
                let isName = function Name _ -> true | _ -> false
                if not (List.forall isName polynomial.variables) then
                    // Variables must be `Name _` for the conversion to be valid, for the moment.
                    PolyEqAsLinEqResult.NotNamedVariables
                else
                    let equation = Equation(kind, Polynomial.Convertion.toSumPow polynomial, Const Zero)            
                    let variables = List.map (function Name var -> var) polynomial.variables

                    match LinearEquation.lineq equation variables with
                    | None -> PolyEqAsLinEqResult.NotLineq
                    | Some lineq -> PolyEqAsLinEqResult.Lineq lineq

        /// If the given polynomial equation system is a linear equation system, then convert it to a system of linear
        /// equation representation. This function does not indicate the cause of the failure (None).
        let public tryAsLinearEquationSystem (PolyEqSystem system) =
            let isLineq = function PolyEqAsLinEqResult.Lineq _ -> true | _ -> false

            let lst = List.map tryAsLinearEquation system

            if List.forall isLineq lst then
                let mapper = function
                    PolyEqAsLinEqResult.Lineq lineq ->
                        List.ofSeq (LinearEquation.getVariables lineq), lineq

                let result = List.map mapper lst
                let variables, equations = List.unzip result

                if List.forall (( = ) variables.[0]) variables then
                    Some (LinearEquation.LinEqSystem (equations, variables.[0]))
                else
                    None
            else
                None

