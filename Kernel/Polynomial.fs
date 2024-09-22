namespace Liyh.Kernel

#nowarn "3391"
#nowarn "193"
#nowarn "25"
#nowarn "46"
#nowarn "57"

/// Polynomials are extremely important. They are present in a large number of cases.
/// This module enables working with 𝑓 ∈ K[x₁, x₂, ..., xₙ] polynomials of arbitrary finite degrees and variables.
/// The handling of the K field is delegated to SumPow.

[<RequireQualifiedAccess>]
module rec Polynomial =
    open System.Collections.Generic
    open System
    open Liyh.Kernel
    open System.Runtime.CompilerServices
    open Liyh.Kernel.TrueVariable
    open Liyh.Utils

    exception public EmptyPolynomialException
    exception public ExcludedVariableIsVariableException of string
    exception public VariableIsExcludedVariableException of Variable
    exception public ConstantVariablePolynomialException of SumPow list
    exception public NotAPolynomialException of SumPow
    exception public NotUnivariatePolynomialException of Polynomial
    exception public NoCompatiblePolynomialsException of Polynomial list
    exception public ZeroPolynomialDivisionException of Polynomial
    exception public PolynomialVariablesNotEquivalentException of variables: Variable list * vorder: Variable list
    exception public DerivativeWRTNonFoundVariableException of Polynomial * Variable
    exception public IntegrationWRTNonFoundVariableException of Polynomial * Variable
    exception public HighestDegreeNotMatchNumberOfCoefficientsException of deg: int list * coeffs: SumPow list
    exception public PolynomialNotContainsVariablesException of Polynomial * Variable list
    exception public NotAnExactDivisionException of remainder: SumPow list
    exception public DivisorHasHigherDegreeThanDividendException of divisor: SumPow list * dividend: SumPow list
    exception public DivisorHasHigherDegreeThanDividendException' of divisor: double list * dividend: double list
    exception public DivisionByZeroPolynomialException
    exception public PolynomialHaveNonIntegerCoefficientsException of Polynomial
    exception public RootIsNotIntegerException of SumPow
    exception public ValueIsNotPolynomialRootException of Polynomial * int

    /// We define different multivariate monomial orders (this also reduce to the well known ordering in the univariate case).
    module private Ordering =

        // Here we define the three standard monomial orders:
        //
        //  - Lexicographic order (`lex`)
        //  - Graded lexicographic order (`grlex`)
        //  - Graded reverse lexicographic order (`grevlex`)
        //
        // See https://en.wikipedia.org/wiki/Monomial_order.
        // By default, the multivariate polynomial representation orders its monomials according to the `currentOrdering` order.
        // This value cannot currently be modified by the user at runtime given the way we select the order (see below).

        [<Literal>]
        let private GREATER = 1

        [<Literal>]
        let private LESSER = -1

        /// Lexicographic order.
        let inline public lex (ord1: int list) (ord2: int list) =
            match List.tryFind ((<>) 0) (List.map2 (-) ord1 ord2) with
            | Some d when d > 0 -> GREATER
            | _ -> LESSER

        /// Reversed lexicographic order.
        let inline private revlex (ord1: int list) (ord2: int list) =
            match List.tryFindBack ((<>) 0) (List.map2 (-) ord1 ord2) with
            | Some d when d < 0 -> GREATER
            | _ -> LESSER

        /// Graded lexicographic order.
        let inline public grlex (ord1: int list) (ord2: int list) =
            let s1 = List.sum ord1
            let s2 = List.sum ord2

            if s1 > s2 then GREATER
            elif s1 = s2 then lex ord1 ord2
            else LESSER

        /// Graded reverse lexicographic order.
        let inline public grevlex (ord1: int list) (ord2: int list) =
            let s1 = List.sum ord1
            let s2 = List.sum ord2

            if s1 > s2 then GREATER
            elif s1 = s2 then revlex ord1 ord2
            else LESSER

    /// The current implementation defaults to lexicographical order.
    let private currentOrdering = Ordering.lex

    /// Implements the degree of a monomial as a simple list of positive integers (e.g. `3x²yz³ -> [2; 1; 3]`). The interest in
    /// defining such a singular type lies in the implementation of a very particular order that monomials have to follow in the
    /// plynomial representation, described by `currentOrdering`. Not all calculations require polynomials to be ordered,
    /// but making this order automatic simplifies matters. See https://en.wikipedia.org/wiki/Monomial_order.
    [<Struct; CustomComparison; CustomEquality>]
    type public MonomialDegree =
        | MonomialDegree of int list

        member this.Item(index: int) =
            match this with
            | MonomialDegree deg -> deg.[index]

        /// Returns the list of integers corresponding to the individual degrees.
        member this.GetList =
            match this with
            | MonomialDegree lst -> lst

        // Implement the graded reverse lexicographic order.
        interface IComparable with
            member ord1.CompareTo obj =
                let (MonomialDegree ord1) = ord1

                match obj with
                | :? MonomialDegree as (MonomialDegree ord2) -> if ord1 = ord2 then 0 else currentOrdering ord1 ord2

                | _ -> invalidArg "obj" "cannot compare value of different types"

        override ord1.Equals obj =
            let (MonomialDegree ord1) = ord1

            match obj with
            | :? MonomialDegree as (MonomialDegree ord2) -> ord1 = ord2
            | _ -> false

        override ord.GetHashCode() =
            let (MonomialDegree ord) = ord in HashCode.Combine(MonomialDegree, hash ord)

    /// In the broadest sense, we define a variable as an expression containing one or more "true variables". For example, we
    /// might have the following expression: `P ≡ 3cos[x]² - 7y³Cos[x] + 2`. This can be seen as a multivariate polynomial in the
    /// two variable `Cos[x]` and `y`. The "true variables" are `x` and `y`. By substituting `α := Cos[x]` and `β := y` we have
    /// indeed a more recognizable multivariate polynomial `P ≡ 3α² - 7αβ³`. Hence the simple type alias.
    type public Variable = SumPow

    /// Implements the "Monomial" representation, simplifying the use of polynomial terms.
    [<AutoOpen>]
    module public Monomial =

        /// A monomial consists of a coefficient and a list of variables associated with an exponent.
        type public Monomial = SumPow * (Variable * int) list // Coefficient × Monomial variable vector

        /// Makes the internal structure of the two given monomials compatible.
        let public compatibleMonomial (m1: Monomial) (m2: Monomial) =
            let p1 = fromMonomials [ m1 ]
            let p2 = fromMonomials [ m2 ]

            let p1, p2 = compatible p1 p2
            leadingTerm p1, leadingTerm p2

        /// Gets the list of exponents of the given monomial.
        let inline public monomialExponentVector ((_, xs): Monomial) = List.map snd xs

        /// An active pattern for identifying a multivariate (or univariate) monomial given given the variables as well as the
        /// variables that are not unknowns of the monomial.
        let public (|Monomial|_|) (variables: SumPow list) (excludedVariables: string list) (expr: SumPow) : Monomial option =

            /// Retrieves the integer powers of the variable part of the monomial.
            let retrieveDegree =
                List.map (function
                    | (_, PureConstantExpression.PureConstantExpressionInteger degree) -> degree
                    | _ -> failwith "??")

            match Simplification.simplify expr with
            | Prod prod ->
                let trueVariables = manyTrueVariables variables excludedVariables

                let vpart, cpart =
                    List.partition (fun (b, p) -> Misc.isPureConstInteger p && List.contains b variables) prod

                let cpart = Misc.prodToSumPow cpart |> Simplification.simplify

                if containsVariables cpart trueVariables then
                    None
                else
                    let monomial = List.map2 (fun (b, _) p -> (b, p)) vpart (retrieveDegree vpart)

                    Some(cpart, monomial)

            | Power(b, PureConstantExpression.PureConstantExpressionInteger p) when List.contains b variables -> Some(SumPow.Const One, [ (b, p) ])

            | v when List.contains v variables -> Some(SumPow.Const One, [ (v, 1) ])

            | _ -> None

        /// If possible, return a monomial in the given variables. Otherwise returns `None`.
        let inline public tryMonomial (variables: SumPow list) (excludedVariables: string list) (expr: SumPow) : Monomial option =

            match expr with
            | Monomial variables excludedVariables monomial -> Some monomial
            | _ -> None

        /// Gets the list of monomials of the given polynomial.
        let inline public getMonomials { variables = variables; polynomial = polynomial } : Monomial list =

            Map.toList polynomial
            |> List.map (function
                | MonomialDegree degs, coeff -> coeff, List.map2 tuple2 variables degs)

        /// Checks if the monomial `m1` is divisible by the monomial `m2`.
        let public isDivisibleBy (m1: Monomial) (m2: Monomial) =
            let m1, m2 = compatibleMonomial m1 m2

            List.map2 (<=) (monomialExponentVector m2) (monomialExponentVector m1)
            |> List.forall id
        //List.map2 (fun a b -> a <> 0 && a <= b) (monomialExponentVector m2) (monomialExponentVector m1) |> List.forall id

        /// If `m1` is divisible by `m2`, then returns `Some(m1/m2)` else returns `None`.
        let private monomialDivision (m1: Monomial) (m2: Monomial) : Monomial option =
            let m1, m2 = compatibleMonomial m1 m2

            if not (isDivisibleBy m1 m2) then
                None
            else

                let coeff = fst m1 / fst m2
                let m = List.map2 (fun (v, b) (_, a) -> v, (b - a)) (snd m1) (snd m2) // (v1 ≡ v2)

                Some(coeff, m)

        /// Performs monomial division if the divisor monomial divides the dividend monomial, else returns `None`.
        let public (/?) = monomialDivision

        /// Calculate the GCD of the two given monomial.
        let public monomialGCD (m1: Monomial) (m2: Monomial) : Monomial =
            let m1, m2 = compatibleMonomial m1 m2
            let monomial = List.map2 (fun (v, a) (_, b) -> v, min a b) (snd m1) (snd m2)
            SumPow.Const One, monomial

        /// Convert the given monomial to the SumPow representation.
        let inline public monomialToSumPow ((coeff, monomial): Monomial) =
            List.fold (fun acc (var, deg) -> acc * (var ** deg)) coeff monomial

    /// Represents a general multivariate polynomial with variables and coefficients in SumPow. The representation consists
    /// of a list of the polynomial's variables and its coefficients in the form of a Map whose keys are the degrees of each
    /// monomial (like a list of integers ordered according to the defined order of the variables) and whose values are the
    /// coefficients. For example, consider the polynomial `3x²y - y + 2x + 5`. Il will be encoded as the Map
    /// `{ ([2; 1], 3); ([0; 1], -1); ([1; 0]; 2); ([0; 0], 5) }`. Order is important!
    /// Thus, a univariate polynomial will be equivalent to a simple `Map<degree, coefficient>` and a given variable.
    ///
    /// A polynomial is a `ISymbolic`.
    [<Symbolic>]
    type public Polynomial =
        { variables: Variable list // The list of generalized variables
          polynomial: Map<MonomialDegree, SumPow> // The multivariate polynomial representation
          excludedVariables: string list } // The list of true-variables that are not part of the variables

        interface ISymbolic with
            member this.ToSymbolic() = toSymbolic this
            member this.ToLatex() = Some(toLatex this)
            member this.ToLatexOrString() = toLatex this
            member this.Hash = hash this

        static member op_Addition(p1: Polynomial, p2: Polynomial) = PolynomialOperations.addition p1 p2
        static member op_Addition(p: Polynomial, sp: SumPow) = PolynomialOperations.additionBySumPow p sp
        static member op_Addition(p: Polynomial, m: Monomial) = PolynomialOperations.additionByMonomial p m
        static member op_Subtraction(p1: Polynomial, p2: Polynomial) = PolynomialOperations.subtraction p1 p2
        static member op_Subtraction(p: Polynomial, sp: SumPow) = PolynomialOperations.subtractionBySumPow p sp
        static member op_Subtraction(p: Polynomial, m: Monomial) = PolynomialOperations.subtractionByMonomial p m
        static member op_Division(p1: Polynomial, sp: SumPow) = PolynomialOperations.diviseBySumPow p1 sp
        static member op_Multiply(p1: Polynomial, p2: Polynomial) = PolynomialOperations.multiply p1 p2
        static member op_Multiply(p: Polynomial, sp: SumPow) = PolynomialOperations.multiplyBySumPow p sp
        static member op_Multiply(sp: SumPow, p: Polynomial) = PolynomialOperations.multiplyBySumPow p sp
        static member op_Multiply(p: Polynomial, m: Monomial) = PolynomialOperations.multiplyByMonomial p m
        static member op_Multiply(m: Monomial, p: Polynomial) = PolynomialOperations.multiplyByMonomial p m
        static member Pow(p: Polynomial, n: int) = PolynomialOperations.integerPower p n

    module public PolynomialOperations =

        /// Adds two polynomials, coefficient by corresponding coefficient. If a monomial of one of the two polynomials has no
        /// corresponding monomial, then append this monomial to the resulting polynomial.
        let public addition (p1: Polynomial) (p2: Polynomial) =
            if isZeroPolynomial p1 then
                p2
            else if isZeroPolynomial p2 then
                p1
            else

                let p1, p2 = compatible p1 p2

                let inline mapper _ c1 c2 = Simplification.simplify (c1 + c2)
                let poly = Map.join p1.polynomial p2.polynomial mapper
                let poly = Map.filter (konst (not << Misc.isZero)) poly

                { p1 with polynomial = poly }

        let public additionBySumPow (p: Polynomial) (sp: SumPow) =
            if Misc.isZero sp then p else
            { p with
                polynomial = Map.addOrUpdate (MonomialDegree(List.map (konst 0) p.variables)) sp p.polynomial ((+) sp) }

        let public additionByMonomial (p: Polynomial) (m: Monomial) = p + fromMonomials [ m ]

        /// Same as addition, but having mapped each coefficient by a `-1` product.
        let public subtraction (p1: Polynomial) (p2: Polynomial) =
            let p2 =
                { p2 with
                    polynomial = Map.mapKeyValue (fun (k, v) -> k, -v) p2.polynomial }

            addition p1 p2

        let public subtractionBySumPow (p: Polynomial) (sp: SumPow) =
            { p with
                polynomial = Map.addOrUpdate (MonomialDegree(List.map (konst 0) p.variables)) sp p.polynomial ((-) sp) }

        let public subtractionByMonomial (p: Polynomial) (m: Monomial) = p - fromMonomials [ m ]

        /// Multiply each coefficient of the given polynomial by the given expression.
        let public multiplyBySumPow (p: Polynomial) (sp: SumPow) =
            { p with
                polynomial = Map.map (fun _ v -> v * sp) p.polynomial }

        /// The "naive" polynomial multiplication algorithm, in 𝒪(n²) in the theoretical worst case. This algorithm is
        /// too slow for polynomials with several hundred terms, but this might not happen very often in practice. This
        /// function handles both the univariate and multivariate cases generally (which also has an impact on performance).
        [<MethodImpl(MethodImplOptions.AggressiveOptimization)>]
        let private naiveMultiply (p1: Polynomial) (p2: Polynomial) =
            let p1, p2 = compatible p1 p2

            let inline eachTerm (MonomialDegree deg1) coeff1 acc (MonomialDegree deg2) coeff2 =
                let deg' = MonomialDegree(List.map2 (+) deg1 deg2)
                let coeff' = Simplification.simplify (coeff1 * coeff2)

                Map.addOrUpdate deg' coeff' acc ((+) coeff')

            let inline eachMonomial result deg1 coeff1 =
                let t = Map.fold (eachTerm deg1 coeff1) Map.empty p2.polynomial
                Map.join result t (fun _ c1 c2 -> Simplification.simplify (c1 + c2))

            { p1 with
                polynomial = Map.fold eachMonomial Map.empty p1.polynomial }

        /// Implements Karatsuba's algorithm for fast multiplying univariate polynomials.
        /// See https://en.wikipedia.org/wiki/Karatsuba_algorithm.
        [<RequireQualifiedAccess>]
        module private Karatsuba =

            // The Karatsuba algorithm is a so-called ‘fast’ multiplication algorithm (of time complexity 𝒪(n^1.58)
            // instead of 𝒪(n²) for the naive algorithm) implemented here for univariate polynomials.
            // The generalisation to multivariate polynomials is more difficult and might be added in a future update.
            //
            // The methods in this module are specialised to the univariate case, making even a small multiplication
            // much more efficient than the default version of `PolynomialOperations.naiveMultiply`.

            let inline private add (p1: SumPow array) (p2: SumPow array) =
                let len1 = Array.length p1
                let len2 = Array.length p2
                let maxLen = max len1 len2
                let result = Array.create maxLen (Const Zero)

                for i = 0 to maxLen - 1 do
                    let v1 = if i < len1 then p1.[i] else Const Zero
                    let v2 = if i < len2 then p2.[i] else Const Zero
                    result.[i] <- v1 + v2
                result

            let inline private sub (p1: SumPow array) (p2: SumPow array) =
                add p1 (Array.map (( * ) -1) p2)

            let inline private split (p: SumPow array) (n: int) =
                let mid = n / 2
                (p.[..mid - 1], p.[mid..])

            let inline private shiftExponent (p: SumPow array) (n: int) =
                let len = Array.length p
                let result = Array.create (len + n) (Const Zero)

                Array.blit p 0 result n len
                result

            /// Faster version of naive polynomial multiplication for univariate polynomials.
            let private basicMultiply (p1: SumPow array) (p2: SumPow array) =
                let len1 = Array.length p1
                let len2 = Array.length p2
                let result = Array.create (len1 + len2 - 1) (Const Zero)

                Array.iteri (fun i x1 ->
                    for j = 0 to len2 - 1 do
                        result.[i + j] <- result.[i + j] + x1 * p2.[j]) p1

                result

            /// Implements Karatsuba's algorithm for fast multiplying univariate polynomials.
            /// The univariate polynomial is represented as an array of its coefficients.
            /// See https://en.wikipedia.org/wiki/Karatsuba_algorithm.
            let rec private karatsubaMultiply (p1: SumPow array) (p2: SumPow array) =
                if Array.length p1 <= 30 && Array.length p2 <= 30 then basicMultiply p1 p2
                else
                    let n = max (Array.length p1) (Array.length p2)
                    let n = if n % 2 = 0 then n else n - 1

                    let (a0, a1) = split p1 n
                    let (b0, b1) = split p2 n

                    let U = karatsubaMultiply a0 b0
                    let Z = karatsubaMultiply a1 b1
                    let Y = karatsubaMultiply (add a0 a1) (add b0 b1)

                    let Y = sub Y (add U Z)
                    let Y = shiftExponent Y (n / 2)
                    let Z = shiftExponent Z n

                    add (add U Z) Y

            /// Implements Karatsuba's algorithm for fast multiplying univariate polynomials.
            /// See https://en.wikipedia.org/wiki/Karatsuba_algorithm.
            let public multiply (p1: Polynomial) (p2: Polynomial) =
                let P = completeCoefficients p1
                let Q = completeCoefficients p2

                let P, Q =
                    let nP, nQ = List.length P, List.length Q
                    let P, Q = Array.ofList P, Array.ofList Q

                    if   nP < nQ then Array.append    [| for _ in 0 .. (nQ - nP) - 1 do Const Zero |] P, Q
                    elif nP > nQ then P, Array.append [| for _ in 0 .. (nP - nQ) - 1 do Const Zero |] Q
                    else P, Q

                let result = karatsubaMultiply P Q
                fromCoefficients p1.variables [ Array.length result ] (List.ofArray result)

        /// Implements Karatsuba's algorithm for fast multiplying univariate polynomials.
        /// See https://en.wikipedia.org/wiki/Karatsuba_algorithm.
        let inline private karatsubaMultiply (p1: Polynomial) (p2: Polynomial) =
            if not (isUnivariate p1) then raise (NotUnivariatePolynomialException p1)
            if not (isUnivariate p2) then raise (NotUnivariatePolynomialException p2)

            if not (List.length p1.variables = 1) then failwith "The polynomial is univariate but of multivariate structure"
            if not (List.length p2.variables = 1) then failwith "The polynomial is univariate but of multivariate structure"

            compatible p1 p2 ||> Karatsuba.multiply

        /// Polynomial multiplication.
        let public multiply (p1: Polynomial) (p2: Polynomial) =
            if isZeroPolynomial p1 || isZeroPolynomial p2
            then zeroPolynomial p1.variables
            else

                // A fast multiplication algorithm is used in the univariate case.
                // Otherwise, a slower but general multiplication is used.

                //if isUnivariate p1 && isUnivariate p2

                (* Because of the difficulties of generalising to multivariate polynomials,
                   only restricted univariate polynomials are accepted... *)

                if List.length p1.variables = 1 && List.length p2.variables = 1
                then karatsubaMultiply p1 p2
                else naiveMultiply p1 p2

        /// Multiply each coefficient of the given polynomial by the given monomial.
        let public multiplyByMonomial (p: Polynomial) (m: Monomial) =
            compatible p (fromMonomials [ m ]) ||> multiply

        let public diviseBySumPow (p: Polynomial) (sp: SumPow) =
            if Misc.isZero sp then
                raise (ZeroPolynomialDivisionException p)

            if Misc.isOne sp then p else
            { p with
                polynomial = Map.map (fun _ value -> value / sp) p.polynomial }

        // This code is actually slower than the trivial implementation. The algorithm reduces the number of multiplications
        // but increases the size of the polynomials to be multiplied, so the efficiency of the procedure relies on the
        // efficiency of the polynomial multiplication (currently, naive multiplication is implemented).
        let rec public integerPowerBySquaring (p: Polynomial) (n: int) =
            if n < 0 then failwith "todo"
            elif n = 0 then { p with polynomial = Map.singleton (MonomialDegree (List.map (konst 0) p.variables)) (SumPow.Const One) }
            elif n % 2 = 0 then integerPowerBySquaring (p * p) (n / 2)
            else p * integerPowerBySquaring (p * p) ((n - 1) / 2)

        let public integerPower (p: Polynomial) (n: int) =
            // Naive implementation.
            // `SumPow.Expand.fullExpand` is way faster for "large" exponents
            match n with
            | n when n < 0 -> failwith "todo" // Division
            | 0 -> { p with polynomial = Map.singleton (MonomialDegree (List.map (konst 0) p.variables)) (SumPow.Const One) }
            | n -> Array.reduce ( * ) (Array.init n (konst p))

    /// This module implements methods for working with structurally different polynomials, making them compatible.
    /// By construction, a polynomial is represented as a structure of two fields: the first consists of the list of variables,
    /// and the second of a dictionary whose keys are the degrees associated with the variables and the values the coefficient,
    /// thus forming a collection of monomials. Each monomial degree is a list of naturals that is ordered according to the lis
    /// of variables. Thus, two polynomials are compatible if they have the same list of variables. The aim of the compatibility
    /// function is to modify this structure in the polynomials involved, so that in the end they each have the same variables.
    [<AutoOpen>]
    module private PolynomialCompatibility =

        /// Adapts the internal structure of the given polynomial to match the order of the given variables.
        let inline public reorder ({ variables = variables; polynomial = polynomial } as p) (vorder: SumPow list) =

            if not (List.areEquivalent variables vorder) then
                raise (PolynomialVariablesNotEquivalentException(variables, vorder))

            if variables = vorder then
                p
            else

                let inline indexMap i =
                    List.findIndex ((=) variables.[i]) vorder

                let inline inner (MonomialDegree degree, coeff) =
                    MonomialDegree(List.permute indexMap degree), coeff

                { p with
                    variables = vorder
                    polynomial = (Map.toArray >> Array.map inner >> Map.ofArray) polynomial }

        /// Reorganizes the internal structure of the given plynomial to extend it to new variables.
        /// Extension to new variables **does not** reorganize the internal order.
        let private extendToNewVariables ({ variables = variables; polynomial = polynomial; excludedVariables = excludedVariables } as p) (newVariables: SumPow list) =

            // We make sure that the variables proposed for extension are not to be excluded.
            match List.tryFindIndex (flip containsVariables excludedVariables) newVariables with
            | Some i -> raise (VariableIsExcludedVariableException variables.[i])
            | None -> ()

            if List.areEquivalent variables newVariables then
                p
            else

                /// The list of new variables to be added.
                let diff = List.except variables newVariables

                if List.isEmpty diff then
                    p
                else // No new variable needs to be added

                    let ext = List.init (List.length diff) (konst 0)

                    let polynomial =
                        Map.mapKeyValue
                            (fun (MonomialDegree degrees, coeff) -> MonomialDegree(degrees @ ext), coeff)
                            polynomial

                    { variables = variables @ diff
                      polynomial = polynomial
                      excludedVariables = excludedVariables }

        let public extendToNewExcludedVariables (p: Polynomial) (excludedVariables: string list) =

            // We make sure that the excluded variables proposed for extension are not already variables.
            match List.tryFindIndex (flip containsVariables excludedVariables) p.variables with
            | Some i -> raise (VariableIsExcludedVariableException p.variables.[i])
            | None ->
                { p with
                    excludedVariables = List.merge p.excludedVariables excludedVariables }

        /// Check whether the two given plynomials are structurally compatible.
        let inline public areCompatible (p1: Polynomial) (p2: Polynomial) =
            let variablesTest = p1.variables = p2.variables

            let excludedVariablesTest () =
                not (List.containsBy (flip containsVariables p1.excludedVariables) p2.variables)
                && not (List.containsBy (flip containsVariables p2.excludedVariables) p1.variables)

            // For two polynomials to be compatible, they must
            //  1. have the same variables (exactly and in the SAME order)
            //  2. not be mutually exclusive in their variables to be excluded.

            variablesTest && excludedVariablesTest ()

        /// Check whether the given plynomials are structurally compatible.
        let inline public areCompatibles (polynomials: Polynomial list) =
            if List.isEmpty polynomials then
                false
            else // The empty polynomial may be compatible after all?
                List.forall (areCompatible polynomials.Head) polynomials

        /// Makes the internal structure of the two given polynomials compatible. The two polynomials returned will then be
        /// compatible for any operation between them, such as for multiplication.
        let public compatible (p1: Polynomial) (p2: Polynomial) =
            if areCompatible p1 p2 then
                (p1, p2)
            else

                let p1' = extendToNewVariables p1 p2.variables
                let p2' = extendToNewVariables p2 p1.variables
                // let excludedVariables' = List.merge p1'.excludedVariables p2'.excludedVariables
                let p1' = reorder p1' p2'.variables

                extendToNewExcludedVariables p1' p2.excludedVariables,
                extendToNewExcludedVariables p2' p1.excludedVariables

                // { p1' with excludedVariables = excludedVariables' },
                // { p2' with excludedVariables = excludedVariables' }

        /// Makes all given polynomials compatible.
        let public compatibles (polynomials: Polynomial list) =

            let rec allCompatible polynomials =
                let rec adjust acc remaining =
                    match remaining with
                    | [] -> List.rev acc
                    | [ x ] -> List.rev (x :: acc)
                    | x :: y :: rest ->
                        let x, y = compatible x y
                        adjust (x :: acc) (y :: rest)

                let newPolynomials = adjust [] polynomials

                if newPolynomials = polynomials then
                    newPolynomials
                else
                    allCompatible newPolynomials

            match polynomials with
            | [] -> []
            | [ p ] -> [ p ]
            | [ p1; p2 ] ->
                let p1, p2 = compatible p1 p2
                [ p1; p2 ]
            | ps -> if areCompatibles ps then ps else allCompatible ps

    [<AutoOpen>]
    module public Convertion =

        /// Convert the polynomial into the equivalent SumPow representation.
        let public toSumPow { variables = variables; polynomial = polynomial } =

            let makeVariables =
                List.map2
                    (fun sp d ->
                        if d <> 0 then
                            Some(Pow(sp, SumPow.Const(double d)))
                        else
                            None)
                    variables

            let inline inner result (MonomialDegree degrees, coeff) =
                if Misc.isZero coeff then result
                else
                    let vs = List.choose id (makeVariables degrees)
                    Term(powId coeff :: vs) :: result

            Map.toList polynomial |> List.fold inner [ termId (Const Zero) ] |> Sum

        /// Generates the univariate polynomial whose roots are specified.
        let public fromRoots (variable: SumPow) (roots: double list) =
            let coefficients = List<double> [ -roots.Head; 1 ]

            for k = 2 to roots.Length do
                coefficients.Add 1

                for i = (k - 2) downto 0 do
                    coefficients.[i + 1] <- coefficients.[i] - roots.[k - 1] * coefficients.[i + 1]

                coefficients.[0] <- -coefficients.[0] * roots.[k - 1]

                if Math.IEEERemainder(k, 2) = 1 then
                    coefficients.[k] <- -coefficients.[k]

            let polynomial =
                let inline mapper deg coeff =
                    MonomialDegree [ deg ], SumPow.Const(Constant coeff)

                Map.ofArray (Array.mapi mapper (Array.ofSeq coefficients))

            { variables = [ variable ]
              polynomial = polynomial
              excludedVariables = [] }

        /// Assuming a list of one or more compatible monomials, convert it into a polynomial.
        let public fromMonomials (monomials: Monomial list) =
            let inline monoDeg mono = MonomialDegree(List.map snd mono)

            match monomials with
            | [] ->
                { variables = []
                  polynomial = Map.empty
                  excludedVariables = [] }

            | [ coeff, mono ] ->
                { variables = List.map fst mono
                  polynomial = Map.singleton (monoDeg mono) coeff
                  excludedVariables = [] }

            | xs ->
                { variables = List.map fst (snd xs.[0])
                  polynomial =
                    Map.ofList (
                        List.map
                            (function
                            | coeff, mono -> monoDeg mono, coeff)
                            xs
                    )
                  excludedVariables = [] }

        /// Construct a polynomial using the given coefficients. The first given coefficient corresponds to the highest-degree
        /// monomial and the last corresponds to the lowest.
        let public fromCoefficients (variables: SumPow list) (highestDegree: int list) (coefficients: SumPow list) =
            if not (List.length variables = List.length highestDegree) then
                raise (HighestDegreeNotMatchNumberOfCoefficientsException (highestDegree, coefficients))

            if List.length variables = 1 then
                { variables = variables
                  polynomial = Map(List.mapiBack (fun i coeff -> MonomialDegree [ i ], coeff) coefficients)
                  excludedVariables = [] }
            else
                // assert (List.length coefficients = List.fold (fun acc a -> acc * (a + 1)) (highestDegree.Head + 1) (List.tail highestDegree))
                let allDegrees =
                    cartProd (List.map (fun d -> [ 0..d ]) highestDegree)
                    |> List.sortWith currentOrdering
                    |> List.rev

                let allDegrees = List.map MonomialDegree allDegrees

                { variables = variables
                  polynomial = Map(List.map2 tuple2 allDegrees coefficients)
                  excludedVariables = [] }

    /// This module contains automatic conversion patterns between SumPow and Polynomial, as well as useful related functions.
    [<AutoOpen>]
    module public Pattern =
        open PureConstantExpression

        /// An active pattern identifying and converting a polynomial expression from the SumPow representation to the
        /// polynomial representation of the given variable. In case of success, the pattern returns the constructed polynomial
        /// part and a “remainder” consisting of all terms not recognized as part of the polynomial expression.
        [<MethodImpl(MethodImplOptions.AggressiveOptimization)>]
        let public (|UnivariatePolynomial|_|) (variable: SumPow) (excludedVariables: string list) (expr: SumPow) =
            if Misc.isPureConst variable then
                raise (ConstantVariablePolynomialException [ variable ])

            /// Retrieves the integer power of the variable part of the (univariate) polynomial.
            let retrieveDegree =
                function
                | [] -> 0 // for x⁰
                | [ Pow(_, PureConstantExpressionInteger degree) ] -> degree
                | _ -> failwith "??" // May not happen

            match Simplification.expandAndSimplify expr with
            | Sum terms ->

                let trueVariables = trueVariables variable excludedVariables

                if List.isEmpty trueVariables then
                    raise (ConstantVariablePolynomialException [ variable ])

                /// Attempts to construct a univariate polynomial in the given variable from the matched sum. The function
                /// returns the constructed polynomial part and a “remainder” consisting of all terms not recognized as
                /// part of the polynomial expression.
                let rec tryBuildPolynomial (result: Map<MonomialDegree, SumPow>) (rest: Term list) =
                    function
                    | [] -> result, rest
                    | Term term :: tail ->
                        // First, we isolate the variable terms (e.g. x²).
                        let vpart, cpart =
                            List.partition
                                (function
                                | Pow(b, _) -> b = variable)
                                term

                        let cpart =
                            if List.isEmpty cpart then
                                SumPow.Const One
                            else
                                Simplification.simplify (Sum [ Term cpart ])

                        // We then check that the part corresponding to the coefficient is neutral in the variable.
                        if containsVariables cpart trueVariables then
                            // If the "constant" part is in fact a function of the true variable involved in the variable, then
                            // don't consider the term as a monomial and add it to the list of terms excluded from the polynomial.
                            tryBuildPolynomial result (Term term :: rest) tail
                        else
                            let degree = MonomialDegree [ retrieveDegree vpart ]

                            let result =
                                Map.addOrUpdate degree cpart result ((+) cpart >> Simplification.simplify)

                            tryBuildPolynomial result rest tail

                match tryBuildPolynomial Map.empty List.empty terms with
                | poly, _ when Map.isEmpty poly -> None
                | poly, rest ->
                    let poly =
                        { variables = [ variable ]
                          polynomial = poly
                          excludedVariables = excludedVariables }

                    let rest =
                        if List.isEmpty rest then
                            None
                        else
                            Some(Simplification.simplify (Sum rest))

                    Some(poly, rest)

            // If the variable is the expression, then it counts as a single-term first-degree polynomial.
            | expr when expr = variable ->
                Some(
                    { variables = [ variable ]
                      polynomial = Map.singleton (MonomialDegree [ 1 ]) (SumPow.Const One)
                      excludedVariables = excludedVariables },
                    None
                )

            // A constant monomial doesn't count as a valid polynomial for simplicity's sake.
            | _ -> None

        /// If possible, return a polynomial in the given variables. Otherwise returns `None`.
        let inline public tryAsUnivariatePolynomial (variable: SumPow) (excludedVariables: string list) =

            function
            | UnivariatePolynomial variable excludedVariables univ -> Some univ
            | _ -> None

        /// An active pattern identifying and converting a polynomial expression from the SumPow representation to the
        /// polynomial representation of the given variables. In case of success, the pattern returns the constructed polynomial
        /// part and a “remainder” consisting of all terms not recognized as part of the polynomial expression.
        [<MethodImpl(MethodImplOptions.AggressiveOptimization)>]
        let public (|MultivariatePolynomial|_|) (variables: SumPow list) (excludedVariables: string list) (expr: SumPow) =

            if not (List.forall (not << Misc.isPureConst) variables) then
                raise (ConstantVariablePolynomialException variables)

            let vlen = List.length variables
            let deg0 = List.init vlen (konst 0) |> MonomialDegree

            /// Retrieves the integer powers of the variable part of the (multivariate) polynomial.
            let retrieveDegree (vpart: Pow list) =
                assert (List.length vpart = vlen) // Might not happen

                List.map
                    (function
                    | Pow(_, PureConstantExpressionInteger degree) -> degree
                    | _ -> failwith "??")
                    vpart

            /// Completes the list of "missing variables" (i.e. zero-powered ones).
            let zeroPowers (vpart: Pow list) =
                List.map
                    (fun var ->
                        match
                            List.tryFind
                                (function
                                | Pow(b, _) -> var = b)
                                vpart
                        with
                        | Some power -> power
                        | None -> Pow(var, SumPow.Const Zero))
                    variables

            if vlen = 1 then
                // faster
                tryAsUnivariatePolynomial variables.[0] excludedVariables expr
            else
                match Simplification.expandAndSimplify expr with
                | Sum terms ->

                    let trueVariables = manyTrueVariables variables excludedVariables

                    if List.isEmpty trueVariables then
                        raise (ConstantVariablePolynomialException variables)

                    /// Attempts to construct a multivariate polynomial in the given variables from the matched sum. The function
                    /// returns the constructed polynomial part and a “remainder” consisting of all terms not recognized as
                    /// part of the polynomial expression.
                    let rec tryBuildPolynomial (result: Map<MonomialDegree, SumPow>) (rest: Term list) =
                        function
                        | [] -> result, rest
                        | Term term :: tail ->
                            let mutable notPolyPart = false
                            let mutable cpart = []

                            let inline projection (variable, _) =
                                // If it turns out that the term is not a valid monomial, there's no point in continuing to sort.
                                if notPolyPart then
                                    -1

                                // The factor being processed is constant.
                                elif not (containsVariables variable trueVariables) then
                                    cpart <- variable :: cpart
                                    -1

                                // The factor being processed is valid.
                                elif List.contains variable variables then
                                    List.findIndex ((=) variable) variables

                                // The factor being processed invalidates the term as a good monomial.
                                else
                                    notPolyPart <- true
                                    -1

                            // First, we isolate each of the variables in the term being processed. We perform a sort that
                            // organizes the partitioned variables according to a common order (given and defined by `trueVariables`
                            // This sorting is very important by definition of the `Polynomial` type. At the same time, the projection
                            // function given to the sort function checks whether the term being processed is indeed a valid polynomial
                            // and modifies the `notPolyPart` variable accordingly. This function also constructs the `cpart` part, the
                            // constant factor with respect to the given variables.

                            let gp =
                                List.groupBy
                                    (function
                                    | Pow(b, _) -> b)
                                    term

                            let gp = List.sortBy projection gp |> List.unzip |> snd |> List.flatten

                            // Check that each power `variable^p` has `p` as natural.
                            if List.any gp (not << function Pow(_, PureConstantExpressionNatural _) -> true | _ -> false) then
                                notPolyPart <- true

                            // If it has been detected that the term being processed is not a valid monomial, then it is ignored
                            // and placed in the list of remaining terms.
                            if notPolyPart then
                                tryBuildPolynomial result (Term term :: rest) tail
                            else
                                // The sorting has been done in such a way that all constants are placed at the beginning of `gp`, so
                                // that the `vart` part for the variables is further down the `gp` list.
                                let vpart = List.skip cpart.Length gp

                                let spVpart = Sum [ Term vpart ] |> Simplification.simplify

                                let result =
                                    // Handle when the variable part is a constant (this is because the sort function doesn't
                                    // sort a list of a single element, so our projection function isn't called).
                                    if not (containsVariables spVpart trueVariables) && List.isEmpty cpart then
                                        let spVpart =
                                            if spVpart = Sum [ Term [] ] then
                                                SumPow.Const 1
                                            else
                                                spVpart

                                        Map.addOrUpdate deg0 spVpart result ((+) spVpart >> Simplification.simplify)
                                    else
                                        // A monomial may not contain an explicit instance of all the variables involved in the
                                        // polynomial, e.g. y⁴ ≡ x⁰y⁴. We therefore apply a correction to show zero powers.
                                        let vpart = if List.length vpart < vlen then zeroPowers vpart else vpart

                                        let degree = MonomialDegree(retrieveDegree vpart)

                                        let cpart =
                                            if List.isEmpty cpart then
                                                SumPow.Const One
                                            else
                                                List.reduce (fun acc a -> Simplification.simplify (acc * a)) cpart

                                        Map.addOrUpdate degree cpart result ((+) cpart >> Simplification.simplify)

                                tryBuildPolynomial result rest tail

                    match tryBuildPolynomial Map.empty List.empty terms with
                    | poly, _ when Map.isEmpty poly -> None
                    | poly, rest ->
                        let poly =
                            { variables = variables
                              polynomial = poly
                              excludedVariables = excludedVariables }

                        let rest =
                            if List.isEmpty rest then
                                None
                            else
                                Some(Simplification.simplify (Sum rest))

                        Some(poly, rest)

                // A constant monomial doesn't count as a valid polynomial for simplicity's sake.
                | _ -> None

        /// If possible, return a polynomial in the given variables. Otherwise returns `None`.
        let inline public tryAsMultivariatePolynomial (variables: SumPow list) (excludedVariables: string list) =

            function
            | MultivariatePolynomial variables excludedVariables multiv -> Some multiv
            | _ -> None

        /// Try generating a multivariate (or univariate, but it makes no difference) polynomial in one or more variables deduced
        /// from the given expression, given also a list of variables that are to be excluded from the "variables" of the polynomial.
        let public (|GeneralPolynomial|_|) (excludedVariables: string list) (expr: SumPow) =
            let expr = Expand.fullExpand expr

            /// Filtering predicate for polyomial variables in the broad sense.
            let polynomialVariablePredicate =
                function
                | PureConstantExpression _, PureConstantExpression _ -> false // a constant is not a variable 🤷
                | _, PureConstantExpressionInteger p -> p >= 0
                | _ -> false

            /// Gets the potential variables, in the sense of the definition of a possible variable for a polynomial.
            let rawVariables =
                List.collect
                    (List.filter polynomialVariablePredicate >> List.map fst)
                    (SimplifiedSum.simplifiedSum' expr)
                |> List.distinct

            let trueVariables = manyTrueVariables rawVariables excludedVariables
            let goodVariables = List.filter (flip containsVariables trueVariables) rawVariables

            tryAsMultivariatePolynomial goodVariables excludedVariables expr

        /// If possible, return a polynomial by identifying variables. Otherwise returns `None`.
        let inline public tryAsGeneralPolynomial (excludedVariables: string list) =

            function
            | GeneralPolynomial excludedVariables poly -> Some poly
            | _ -> None

        /// Checks whether the given SumPow expression is fully polynomial in the given variable, i.e. the expression
        /// contains no non-polynomial terms.
        let inline public isFullyUnivariatePolynomial (variable: SumPow) (excludedVariables: string list) =
            function
            | UnivariatePolynomial variable excludedVariables ({ polynomial = univ }, rest) ->
                not (Map.isEmpty univ) && Option.isNone rest
            | _ -> false

        /// Checks whether the given SumPow expression is fully polynomial in the given variables, i.e. the expression
        /// contains no non-polynomial terms.
        let inline public isFullyMultivariatePolynomial (variables: SumPow list) (excludedVariables: string list) =
            function
            | MultivariatePolynomial variables excludedVariables ({ polynomial = multiv }, rest) ->
                not (Map.isEmpty multiv) && Option.isNone rest
            | _ -> false

        /// Assuming the given SumPow expression is a polynomial in the variable `var`, convert it to the polynomial representation.
        let inline public asUnivariatePolynomial var excludedVariables =
            function
            | UnivariatePolynomial var excludedVariables poly -> poly
            | other -> raise (NotAPolynomialException other)

        /// Assuming the given SumPow expression is a polynomial in the variable `var`, convert it to the polynomial representation.
        let inline public asMultivariatePolynomial vars excludedVariables =
            function
            | MultivariatePolynomial vars excludedVariables poly -> poly
            | other -> raise (NotAPolynomialException other)

        /// Assuming the given SumPow expression is a polynomial, convert it to the polynomial representation.
        let inline public asGeneralPolynomial excludedVariables =
            function
            | GeneralPolynomial excludedVariables poly -> poly
            | other -> raise (NotAPolynomialException other)

    /// Various methods for working with leading monomials (LT, LM, LC), coefficients and degrees.
    [<AutoOpen>]
    module public Tools =

        /// Represents the null polynomial in the given variables.
        let public zeroPolynomial (variables: Variable list) =
            { variables = variables
              polynomial = Map.empty
              excludedVariables = [] }

        /// Checks whether the given polynomial is zero (all its coefficients are zero) or structurally empty.
        let public isZeroPolynomial { polynomial = polynomial } =
            Map.isEmpty polynomial || Map.forall (konst Misc.isZero) polynomial

        /// Check that the given polynomial consists of the monomial of degree 0 and coefficient 1.
        let public isOnePolynomial { polynomial = polynomial } =
            Map.count polynomial = 1
            && let a = Map.toArray polynomial in
               let (MonomialDegree deg), coeff = a.[0] in
               List.forall ((=) 0) deg && coeff = SumPow.Const One

        /// Check if the given polynomial is constant (i.e. contains only the [0, 0, ..., 0] term).
        let public isConstantPolynomial ({ polynomial = polynomial } as p) =
            isZeroPolynomial p
            || (Map.count polynomial = 1
                && let (KeyValue(MonomialDegree deg, _)) = Seq.head polynomial in
                   List.forall ((=) 0) deg)

        /// Gets the array of all coefficients of the given polynomial. The array is ordered in the reverse order of the
        /// monomial ordering defined in the polynomial.
        let inline public getCoefficients { polynomial = polynomial } =
            Map.values polynomial |> Array.ofSeq |> Array.rev

        /// Returns the list of non-zero coefficients.
        let inline public nonZeroCoefficients { polynomial = polynomial } =
            (Map.values >> List.ofSeq >> List.filter (Misc.isZero >> not)) polynomial

        // Let f ∈ K[x₁, x₂, ..., xₙ] be a polynomial with a given monomial order (>). Then,
        //  - LT(f) refers to the leading term of f
        //  - LM(f) refers to the leading monomial of f
        //  - LC(f) refers to the leading coefficient of f
        //
        // Let m ∈ K[x₁, x₂, ..., xₙ] be a monomial of the form C⋅x₁ᵃ¹x₂ᵃ²...xₙᵃⁿ with C ∈ K. Then,
        //  - The "term" of m is m itself: C⋅x₁ᵃ¹x₂ᵃ²...xₙᵃⁿ
        //  - The "monomial" of m is the term without the C coefficient: x₁ᵃ¹x₂ᵃ²...xₙᵃⁿ
        //  - The "coefficient" of m is C.
        //
        // Thus, for example, with f[x, y] = 3x²y + xy² + 1 in the reals field using the lexicographic order,
        //  - LT(f) = 3x²y
        //  - LM(f) = x²y
        //  - LC(f) = 3.

        let public leadingTerm { variables = variables; polynomial = polynomial } : Monomial =
            if Map.isEmpty polynomial then Const Zero, List.map (fun v -> (v, 0)) variables
            else
                let (MonomialDegree deg, coeff) = (|KeyValue|) (Seq.last polynomial)
                coeff, List.map2 tuple2 variables deg

        let public leadingMonomial (p: Polynomial) : Monomial =
            let _, monomial = leadingTerm p
            SumPow.Const One, monomial

        let public leadingCoeff = leadingTerm >> fst

        /// Gets the array of all monomial degrees of the given polynomial. The array is ordered in the reverse order of the
        /// monomial ordering defined in the polynomial.
        let inline public getDegrees { polynomial = polynomial } =
            Map.keys polynomial
            |> Array.ofSeq
            |> Array.map (function
                | MonomialDegree deg -> deg)
            |> Array.rev

        /// Returns the degree (also known as 'order') of the given polynomial. This is the maximum sum of each monomial power.
        let public totalDegree x =
            if isZeroPolynomial x then
                0
            else
                (getDegrees >> Array.map List.sum >> Array.max) x

        /// Returns the multidegree of the given polynomial (the ordering is defined in the polynomial).
        let public multiDegree = leadingTerm >> snd

        /// Returns the coefficient of the constant term of the given polynomial.
        let public getConstantTerm (p: Polynomial) =
            if (isZeroPolynomial p) then Const Zero
            else fst (List.minBy snd (getMonomials p))

    /// Some functions concerning polynomial density, i.e. the ratio between the number of non-zero coefficients
    /// and the total degree of the polynomial.
    module public Density =

        /// Returns the density of the polynomial, i.e. the percentage of coefficients in relation to the degree of the polynomial.
        /// This percentage indicates the proportion of coefficients the polynomial contains.
        let public density (poly: Polynomial) =
            let deg = float (totalDegree poly)
            let nCoeffs = (List.length >> float) (nonZeroCoefficients poly)

            (nCoeffs / (deg + 1.)) * 100.

        /// A polynomial is considered dense if its density is greater than or equal to 60% (this is our definition).
        let public isDense poly = density poly >= 60

        /// A polynomial is considered sparse if its density is less than 60% (this is our definition).
        let public isSparse = isDense >> not

    let private toLatex = toSumPow >> Atomic.toLatexValue
    let private toSymbolic = toSumPow >> Atomic.toSymbolic

    [<AutoOpen>]
    module public Coefficients =
        open PureConstantExpression

        (*
            /// Returns all zero and non-zero coefficients of the polynomial.
            let public completeCoefficients (p: Polynomial) =
                if isZeroPolynomial p then List.empty else

                let hdeg = List.map snd (snd (leadingTerm p))
                let allDegrees = cartProd (List.map (fun d -> [ 0 .. d ]) hdeg)

                [ for deg in allDegrees do
                    Map.tryFind (MonomialDegree deg) p.polynomial
                    |> Option.defaultValue (SumPow.Const 0) ]

                |> List.rev
        *)

        /// Returns all zero and non-zero coefficients of the polynomial.
        let public completeCoefficients (p: Polynomial) =
            if isZeroPolynomial p then List.empty else

            let temp = Map.toArray p.polynomial |> Array.map (fun (MonomialDegree deg, _) -> Array.ofList deg) |> array2D
            let hdeg = [ for c in 0 .. Array2D.length2 temp - 1 -> Array.max temp.[*, c] ]

            let allDegrees = cartProd (List.map (fun d -> [ 0 .. d ]) hdeg)

            [ for deg in allDegrees do
                Map.tryFind (MonomialDegree deg) p.polynomial
                |> Option.defaultValue (Const 0) ]

            |> List.rev

        /// Simplify each coefficient of the given polynomial and remove the zero coefficients from the polynomial.
        let public simplifyCoefficients (p: Polynomial) =
            { p with
                polynomial =
                    p.polynomial
                    |> Map.map (fun _ coeff -> Simplification.expandAndSimplify coeff)
                    |> Map.filter (konst (not << Misc.isZero)) }

        /// Check whether the given univariate polynomial has integer coefficients only.
        let public hasIntegerCoefficients (p: Polynomial) =
            List.forall Misc.isPureConstInteger (completeCoefficients p)

        /// Returns the complete list of coefficients of the given univariate polynomial with integer coefficients.
        let public integerCoefficients (p: Polynomial) =
            if not (hasIntegerCoefficients p) then raise (PolynomialHaveNonIntegerCoefficientsException p)
            List.map (function PureConstantExpressionInteger coeff -> coeff) (completeCoefficients p)

    [<AutoOpen>]
    module public Univariate =

        /// Check whether the given polynomial is univariate.
        let public isUnivariate { variables = variables; polynomial = polynomial } =

            // A polynomial may not be multivariate in its variables list, but only have monomials in the same variable,
            // and thus be univariate by definition.
            let univariateTest () =
                let matrix = List.map (function MonomialDegree deg -> deg) (Seq.toList (Map.keys polynomial))
                List.length (List.filter (flip List.any (( <> ) 0)) (List.transpose matrix)) <= 1

            List.length variables = 1 || univariateTest ()

        /// Check whether the given polynomial is multiunivariate.
        let public isMultivariate = not << isUnivariate

        /// Returns the univariate polynomial variable and its position in the type structure.
        let public getUnivariateVariableAndIndex ({ variables = variables; polynomial = polynomial } as p) =
            if not (isUnivariate p) then
                raise (NotUnivariatePolynomialException p)

            if List.length variables = 1 then List.head variables, 0 else
            if isConstantPolynomial p then failwith "Cannot find the variable in a constant polynomial."

            let indexes = Seq.filter (function MonomialDegree deg -> List.any deg (( <> ) 0)) (Map.keys polynomial)
            let index = match Seq.head indexes with MonomialDegree deg -> List.findIndex (( <> ) 0) deg // lazy filter

            variables.[index], index

        /// Convert multivariate polynomial p ∈ K[x₁, x₂, ..., xᵢ, ..., xₙ] into the univariate polynomial
        /// p' ∈ (k[x₁, x₂, ..., xₙ])[xᵢ] in the polynomial field k[...] and in the unique variable xᵢ.
        ///
        /// For example, let p(x, y, z) = x³yz + x²y² + 3x³ + 2x² + xy + xz + 1 (with x, y, z ∈ K) then
        /// we can write the univariate polynomial p'(x) = (yz + 3)x³ + (y² + 2)x² + (y + z)x + 1 as a polynomial
        /// in the multivariate polynomial field K[y, z] and with variable x.
        let public asUnivariate (variable: Variable) (p: Polynomial) =
            if not (List.contains variable p.variables) then
                raise (PolynomialNotContainsVariablesException (p, [ variable ]))

            if isUnivariate p then
                p
            else

                let degIndex = List.findIndex ((=) variable) p.variables
                let variables' = List.removeAt degIndex p.variables

                let variablesAsCoefficients =
                    List.map2 (fun var (deg: int) -> var ** deg) variables'

                let rec inner result =
                    function
                    | [] -> result
                    | (MonomialDegree degs, coeff) :: rest ->
                        let udeg = MonomialDegree [ degs.[degIndex] ]
                        let degs' = List.removeAt degIndex degs
                        let vs = List.filter (not << Misc.isZero) (variablesAsCoefficients degs')
                        let coeff' = List.reduce ( * ) (coeff :: vs)
                        let result = Map.addOrUpdate udeg coeff' result ((+) coeff')
                        inner result rest

                { p with
                    variables = [ p.variables.[degIndex] ]
                    polynomial = inner Map.empty (Map.toList p.polynomial) }

                |> simplifyCoefficients

        /// Returns the total number of roots that the given univariate polynomial has. The result does not take into account
        /// the multiplicity of roots.
        let public countAllRoots (p: Polynomial) =
            if not (isUnivariate p) then
                raise (NotUnivariatePolynomialException p)

            totalDegree p

    module public Calculus =

        /// Performs the derivative (formally, the partial derivative) of the polynomial in the given variable.
        let public derive (p: Polynomial) (variable: Variable) =
            if not (List.contains variable p.variables) then
                raise (DerivativeWRTNonFoundVariableException(p, variable))

            let varIndex = List.findIndex ((=) variable) p.variables

            let inline newDeg (MonomialDegree deg) =
                MonomialDegree(List.mapi (fun j d -> if j = varIndex then d - 1 else d) deg)

            { p with
                polynomial =
                    Map.mapKeyValue
                        (fun (deg, coeff) ->
                            let d = deg.[varIndex]

                            if d = 0 then deg, SumPow.Const Zero
                            else newDeg deg, d * coeff)
                        p.polynomial }
            |> simplifyCoefficients

        /// Performs the univariate indefinite integral of the given polynomial with respect to the given variable.
        /// The `constant` parameter is for the integration constant to be added.
        let public primitive (p: Polynomial) (variable: Variable) (constant: SumPow) =
            if not (List.contains variable p.variables) then
                raise (IntegrationWRTNonFoundVariableException(p, variable))
            
            let varIndex = List.findIndex (( = ) variable) p.variables

            let inline newDeg (MonomialDegree deg) =
                MonomialDegree(List.mapi (fun j d -> if j = varIndex then d + 1 else d) deg)

            { p with
                polynomial =
                    Map.mapKeyValue
                        (fun (deg, coeff) ->
                            let d = deg.[varIndex]
                            newDeg deg, coeff / (d + 1))
                        p.polynomial } + constant

        /// Evaluate the univariate integral of the given polynomial with respect to the given variable and given the
        /// lower and upper bounds of the definite integral.
        let public integral (p: Polynomial) (variable: Variable) (lowerBound: SumPow) (upperBound: SumPow) =
            if lowerBound = upperBound then SumPow.Const Zero else

            let prim = primitive p variable (SumPow.Const Zero)
            let varIndex = List.findIndex (( = ) variable) p.variables
            let remainingVariables = List.removeAt varIndex p.variables

            let inline integrate (MonomialDegree deg, coeff) =
                let expn = deg.[varIndex]
                let otherVariables = List.map2 ( ** ) remainingVariables (List.removeAt varIndex deg)
                List.reduce ( * ) (coeff * (upperBound ** expn - lowerBound ** expn) :: otherVariables)

            List.fold (fun acc a -> acc + integrate a) (SumPow.Const Zero) (Map.toList prim.polynomial)
            |> Simplification.expandAndSimplify

        let public multiplePrimitive (p: Polynomial) (variables: Variable list) (constant: SumPow) =
            // https://en.wikipedia.org/wiki/Integral#Line_integrals_and_surface_integrals
            0
        
        let public multipleIntegral (p: Polynomial) (variables: Variable list) (bounds: (SumPow * SumPow) list) =

            0

    /// Makes the leading coefficient equal to 1 and divides the other coefficients accordingly.
    let private normalize (p: Polynomial) =
        match leadingCoeff p with
        | One -> p
        | c ->
            { p with
                polynomial = Map.map (fun _ coeff -> coeff / c) p.polynomial }

    /// Substitutes each variable with a given expression, returns unsimplified SumPow.
    let public varSubst (p: Polynomial) (values: Map<Variable, SumPow>) =
        if not (List.areEquivalent p.variables (Seq.toList values.Keys)) then
            raise (NoCompatiblePolynomialsException [ p ])

        let rvars = List.ofSeq values.Keys
        let rvals = List.ofSeq values.Values

        let { polynomial = polynomial } = reorder p rvars

        List.map
            (fun (MonomialDegree degrees, coeff) ->
                let ev = (List.map2 ( ** ) rvals >> List.reduce ( * )) degrees
                coeff * ev |> termId)
            (Map.toList polynomial)

        |> SumPow.Sum

    /// Returns the reciprocal polynomial of the given polynomial using the default monomial ordering.
    let public reciprocalPolynomial (p: Polynomial) =
        let degrees, coefficients = Array.unzip (Map.toArray p.polynomial)
        let coefficients' = Array.rev coefficients
        let poly = Map.ofArray (Array.zip degrees coefficients')

        { p with polynomial = poly }

    // This module implement stuff about primitive part and content.
    // See https://en.wikipedia.org/wiki/Primitive_part_and_content.
    module public PrimitiveAndContent =

        /// Returns the content of the integer-coefficients given polynomial.
        /// See https://en.wikipedia.org/wiki/Primitive_part_and_content.
        let public content (p: Polynomial) =
            if not (hasIntegerCoefficients p) then
                raise (PolynomialHaveNonIntegerCoefficientsException p)
            
            List.aggregate intGCD (integerCoefficients p)
            |> double
            |> Constant
            |> Const

        /// Returns the primitive part of the integer-coefficients given polynomial.
        /// See https://en.wikipedia.org/wiki/Primitive_part_and_content.
        let public primitive (p: Polynomial) =
            if not (hasIntegerCoefficients p) then
                raise (PolynomialHaveNonIntegerCoefficientsException p)

            p / content p

        /// Check if the content of the integer-coefficients given polynomial equals 1.
        /// See https://en.wikipedia.org/wiki/Primitive_part_and_content.
        let public isPrimitive (p: Polynomial) =
            if not (hasIntegerCoefficients p) then
                raise (PolynomialHaveNonIntegerCoefficientsException p)
            
            Misc.isOne (content p)

    // This module contains useful algorithms for dividing and factoring polynomials.
    module public Division =
        open Factorization

        exception public InfiniteLoopDuringPolynomialReductionException

        /// In polynomial division, the result is often not a polynomial but a fraction of polynomials.
        [<Symbolic; NoComparison>]
        type public RationalPolynomial =
            { numerator: Polynomial option
              denominator: Polynomial option }

            interface ISymbolic with
                member this.ToLatex () = Some (toLatex this)
                member this.ToLatexOrString () = toLatex this
                member this.ToSymbolic () = toSymbolic this
                member this.Hash = hash this

        let private toLatex { numerator = num; denominator = den } =
            match num, den with
            | Some num, Some den -> sprintf @"\frac{%s}{%s}" (toLatexValue num) (toLatexValue den)
            | Some num, None -> toLatexValue num
            | None, Some den -> sprintf @"\frac{1}{%s}" (toLatexValue den)
            | None, None -> failwith "??" // May not happen

        let private toSymbolic { numerator = num; denominator = den } =
            match num, den with
            | Some num, Some den -> Atomic.toSymbolic (toSumPow num / toSumPow den)
            | Some num, None -> Atomic.toSymbolic num
            | None, Some den -> Atomic.toSymbolic (1 / toSumPow den)
            | None, None -> failwith "??" // May not happen

        let inline public isSimplePolynomial { numerator = numerator; denominator = denominator } =
            Option.isNone denominator && Option.isSome numerator

        /// An active pattern identifying and converting a fractional polynomial expression from the SumPow representation to the
        /// rational polynomial representation of the given variables.
        let public (|RationalPolynomial|_|) (variables: SumPow list) (excludedVariables: string list) =
            function
            | Frac(MultivariatePolynomial variables excludedVariables (numerator, None),
                   MultivariatePolynomial variables excludedVariables (denominator, None)) ->
                Some
                    { numerator = Some numerator
                      denominator = Some denominator }
            | _ -> None

        /// Try identifying and converting a fractional polynomial expression from the SumPow representation to the rational
        /// polynomial representation of the given variables.
        let public tryAsRationalPolynomial (variables: SumPow list) (excludedVariables: string list) =
            function
            | RationalPolynomial variables excludedVariables rp -> Some rp
            | _ -> None

        /// An active pattern identifying and converting a fractional polynomial expression from the SumPow representation to the
        /// rational polynomial representation and infer both numerator and denominator variables. The resulting numerator and
        /// denominator variables are made compatible.
        let public (|RationalGeneralPolynomial|_|) (excludedVariables: string list) =
            function
            | Frac(GeneralPolynomial excludedVariables (numerator, None),
                   GeneralPolynomial excludedVariables (denominator, None)) ->

                let numerator, denominator = compatible numerator denominator

                Some
                    { numerator = Some numerator
                      denominator = Some denominator }
            | _ -> None

        /// Try identifying and converting a fractional polynomial expression from the SumPow representation to the rational
        /// polynomial representation.
        let public tryAsRationalGeneralPolynomial (excludedVariables: string list) =
            function
            | RationalGeneralPolynomial excludedVariables rp -> Some rp
            | _ -> None

        /// Converts the rational polynomial into the SumPow representation.
        let public rationalPolynomialToSumPow { numerator = numerator; denominator = denominator } =
            match numerator, denominator with
            | Some num, Some den -> (toSumPow num) / (toSumPow den)
            | Some num, None -> toSumPow num
            | None, Some den -> 1 / toSumPow den
            | None, None -> raise EmptyPolynomialException

        /// Attempt to factor the numerator and denominator of the given univariate rational polynomial.
        let public tryFactoring { numerator = num; denominator = den } =
            if Option.forall (not << isUnivariate) num && Option.forall (not << isUnivariate) den then None else

            match num, den with
            | Some num, Some den ->
                let num, den = compatible num den
                if num.variables <> den.variables then None else

                let var, _ = getUnivariateVariableAndIndex num
                match Factorization.tryFactoring num (Some var), Factorization.tryFactoring den (Some var) with
                | FactoringResult.Univariate univ1, FactoringResult.Univariate univ2 -> Some (Some univ1, Some univ2)
                | _ -> None

            | Some num, None ->
                let var, _ = getUnivariateVariableAndIndex num
                match Factorization.tryFactoring num (Some var) with
                | FactoringResult.Univariate univ1 -> Some (Some univ1, None)
                | _ -> None

            | None, Some den ->
                let var, _ = getUnivariateVariableAndIndex den
                match Factorization.tryFactoring den (Some var) with
                | FactoringResult.Univariate univ1 -> Some (Some univ1, None)
                | _ -> None

            | _ -> None

        // The division of univariate polynomials is "simple" and is performed via Euclidean division extended to polynomials.
        // The proposed implementation uses synthetic division (which is algorithmically better than long division).
        module public Univariate =

            // Note: Long division is only well defined if the degree of the divisor is less than or equal to the degree
            // of the dividend, thus the same hold for synthethic division.

            /// Performs synthetic division (a method for performing Euclidean division of polynomials with better time complexity
            /// than long division) on two purely numerical polynomials. Returns the quotient and remainder of the division.
            [<MethodImpl(MethodImplOptions.AggressiveOptimization)>]
            let public expandedSyntheticDivisionForDoubles (p1: double list) (p2: double list) =
                if List.isEmpty p1 then [], [] else
                if List.isEmpty p2 then raise DivisionByZeroPolynomialException
                if List.length p2 > List.length p1 then
                    raise (DivisorHasHigherDegreeThanDividendException' (p1, p2))

                if List.forall (( = ) 0.) p2 then raise DivisionByZeroPolynomialException
                let (m :: ms) = List.skipWhile ((=) 0.) p2 // We remove the first potential zero coefficients

                let rec inner =
                    function
                    | _, [] -> []
                    | 0, lst -> lst
                    | i, head :: tail ->
                        let extend = List.length tail - List.length ms
                        let coeff = head / m
                        let extendedMs = ms @ List.replicate extend 0.
                        let updatedList = List.map2 (+) tail (List.map (( * ) -coeff) extendedMs)

                        coeff :: inner ((i - 1), updatedList)

                let indx = List.length p1 - List.length p2 + 1
                let quotient, remainder = List.splitAt indx (inner (indx, p1))
                List.skipWhile (( = ) 0.) quotient, List.skipWhile (( = ) 0.) remainder

            /// Performs synthetic division (a method for performing Euclidean division of polynomials with better time complexity
            /// than long division) on two SumPow polynomials. Returns the quotient and remainder of the division. If both
            /// polynomials are purely numerical, then the calculation is optimized.
            [<MethodImpl(MethodImplOptions.AggressiveOptimization)>]
            let public expandedSyntheticDivision (p1: SumPow list) (p2: SumPow list) =
                let arePureConstantCoefficients = List.forall Misc.isPureConst

                // Handle the case where the dividend is null.
                if List.isEmpty p1 then [], [] else
                if List.length p2 > List.length p1 then raise (DivisorHasHigherDegreeThanDividendException (p1, p2))
                if List.forall Misc.isZero p2 then raise DivisionByZeroPolynomialException

                // If the two polynomials are purely numerical, then the calculation is delegated to a same function but
                // working only with doubles, avoiding the overhead of SumPow's algebraic types.

                if arePureConstantCoefficients p1 && arePureConstantCoefficients p2 then
                    let p1 = List.map (NumericEvaluation.evaluate0 >> toDouble) p1
                    let p2 = List.map (NumericEvaluation.evaluate0 >> toDouble) p2

                    let quotient, remainder = expandedSyntheticDivisionForDoubles p1 p2
                    List.map (Constant >> SumPow.Const) quotient, List.map (Constant >> SumPow.Const) remainder
                else
                    if List.isEmpty p2 then raise EmptyPolynomialException

                    let (m :: ms) = List.skipWhile ((=) (SumPow.Const 0)) p2 // We remove the first potential zero coefficients

                    let rec inner =
                        function
                        | _, [] -> []
                        | 0, lst -> lst
                        | i, head :: tail ->
                            let extend = List.length tail - List.length ms
                            let coeff = head / m
                            let extendedMs = ms @ List.replicate extend (SumPow.Const 0)
                            let updatedList = List.map2 (+) tail (List.map (( * ) -coeff) extendedMs)

                            coeff :: inner ((i - 1), updatedList)

                    let indx = List.length p1 - List.length p2 + 1
                    let quotient, remainder = List.splitAt indx (inner (indx, p1))
                    List.skipWhile Misc.isZero quotient, List.skipWhile Misc.isZero remainder

            /// Performs long division of `p1` by `p2` and returns the quotient and remainder as polynomials.
            let public udiv (p1: Polynomial) (p2: Polynomial) =
                if not (isUnivariate p1) then raise (NotUnivariatePolynomialException p1)
                if not (isUnivariate p2) then raise (NotUnivariatePolynomialException p2)

                let p1, p2 = compatible p1 p2
                let _, varIndex = getUnivariateVariableAndIndex p1

                let ps1 = completeCoefficients p1
                let ps2 = completeCoefficients p2

                let inline hdeg p = [ for i = 0 to List.length p1.variables - 1 do if i = varIndex then List.length p - 1 else 0 ]

                let quotient, remainder = expandedSyntheticDivision ps1 ps2

                let quotient = fromCoefficients p1.variables (hdeg quotient) quotient
                let remainder = fromCoefficients p1.variables (hdeg remainder) remainder

                quotient, remainder

            /// Perform the univariate division of p1 by p2, assuming that the remainder of the division is zero. This case occurs
            /// in particular when p2 is the GCD of p1, which by definition results in a zero remainder. The return is a polynomial.
            let public exactDivision (p1: Polynomial) (p2: Polynomial) (varIndex: int) =
                let quotient, rem = expandedSyntheticDivision (completeCoefficients p1) (completeCoefficients p2)
                let inline hdeg p = [ for i = 0 to List.length p1.variables - 1 do if i = varIndex then List.length p - 1 else 0 ]
                if not (List.isEmpty (List.filter (not << Misc.isZero) rem)) then raise (NotAnExactDivisionException rem)

                fromCoefficients p1.variables (hdeg quotient) quotient

        // Division of multivariate polynomials is less straightforward than univariate division. In fact, we're more
        // likely to talk about a ‘reduction’ instead. It should also be noted that the multivariate division is defined
        // up to a monomial order and is not unique. We need it for the Buchberger algorithm.
        module public Multivariate =

            // P͟e͟r͟f͟o͟r͟m͟a͟n͟c͟e͟ ͟n͟o͟t͟e͟: The reduction in the specific case of two univariate polynomials is really fast using the
            // synthetic univariate division compared to general reduction with `reduce` (according to our benchmarks, it's
            // about 25x faster for integer coefficients and about half for non-integers one!). This specific case should
            // therefore be implemented to redirect the calculation of the reduction where possible.

            /// The result of the reduction ("generalized polynomial division") consists of a list of quotients associated
            /// with the polynomial divisor and a remainder of the division.
            [<NoEquality; NoComparison>]
            type public Reduce =
                { quotients: Map<Polynomial, Polynomial>
                  remainder: Polynomial }

            /// Implement the "division algorithm" for multivariate polynomial. Returns a list of quotients and their associated
            /// divisor polynomials in the form of a dictionary, together with the remainder of the division.
            /// See https://en.wikipedia.org/wiki/Gr%C3%B6bner_basis#Reduction.
            /// Note: the result of the reduction is not unique in general.
            let public reduce (p: Polynomial) (fs: Polynomial list) =
                let (p :: fs) = compatibles (p :: fs)
                let fs = List.removeMany (( = ) p) fs
                let zeroPolynomial = zeroPolynomial p.variables

                let mutable p = p
                let mutable remainder = zeroPolynomial

                // Create the list of the quotients that will result from the algorithm
                // associated with their original polynomials.
                let mutable quotients =
                    (dict >> Dictionary) (List.map (flip tuple2 zeroPolynomial) fs)

                // Theoretically, this loop must ends.
                while not (isZeroPolynomial p) do
                    let mutable divisionOccurred = false
                    let mutable ltp = leadingTerm p

                    let mutable i = 0

                    while i < List.length fs && divisionOccurred = false do
                        let fᵢ = fs.[i]
                        let ltfᵢ = leadingTerm fᵢ

                        match ltp /? ltfᵢ with
                        | Some divisionResult ->
                            quotients.[fᵢ] <- quotients.[fᵢ] + divisionResult
                            p <- p - divisionResult * fᵢ
                            ltp <- leadingTerm p
                            divisionOccurred <- true

                        | None ->
                            i <- i + 1

                    if divisionOccurred = false then
                        remainder <- remainder + ltp
                        p <- p - ltp

                // Convert dictionary to Map.
                let quotients = Map.ofSeq (Seq.map (|KeyValue|) quotients)

                { quotients = quotients;
                  remainder = remainder }

        /// Returns the remainder of the division of `p1` by `p2`, two arbitrary polynomials. If the polynomials are
        /// multivariate, then use the default `currentOrdering` order.
        let public remainder (p1: Polynomial) (p2: Polynomial) =
            (Multivariate.reduce p1 [ p2 ]).remainder

        /// Euclidean GDC algorithm adapted to univariate polynomials.
        let rec private univariateGcd (p1: Polynomial) (p2: Polynomial) =
            if isZeroPolynomial p2 then p1 else
            univariateGcd p2 (remainder p1 p2)

        /// Euclidean GDC algorithm adapted to any polynomials.
        let public polynomialGCD (p1: Polynomial) (p2: Polynomial) =
            if isUnivariate p1 && isUnivariate p2 then
                compatible p1 p2 ||> univariateGcd |> normalize
            else
                failwith "TODO: multivariate GCD"

    // This module implements some elements around resultants.
    // See https://en.wikipedia.org/wiki/Resultant.
    module public Resultant =

        /// Calculate the Sylvester matrix associated with the two given polynomials.
        /// See https://en.wikipedia.org/wiki/Sylvester_matrix.
        let public sylvesterMatrix (p1: Polynomial) (p2: Polynomial) =
            if not (isUnivariate p1) then raise (NotUnivariatePolynomialException p1)
            if not (isUnivariate p2) then raise (NotUnivariatePolynomialException p2)

            let p1, p2 = compatible p1 p2
            let m, n = totalDegree p1, totalDegree p2
            let size = m + n

            let coeffs1 = completeCoefficients p1
            let coeffs2 = completeCoefficients p2

            let inline initializer i j =
                if i < n then
                    let shift = i
                    if j >= shift && j - shift < m + 1 then
                        coeffs1.[j - shift]
                    else
                        SumPow.Const Zero
                else
                    let shift = i - n
                    if j >= shift && j - shift < n + 1 then
                        coeffs2.[j - shift]
                    else
                        SumPow.Const Zero

            Array2D.init size size initializer

        /// Calculate the resultant of the two given univariate polynomials.
        /// See https://en.wikipedia.org/wiki/Resultant.
        let public resultant (p1: Polynomial) (p2: Polynomial) =
            if not (isUnivariate p1) then raise (NotUnivariatePolynomialException p1)
            if not (isUnivariate p2) then raise (NotUnivariatePolynomialException p2)

            let p1, p2 = compatible p1 p2

            let rec loop u v =
                let m = totalDegree u
                let n = totalDegree v

                if n = 0 then
                    leadingCoeff v ** m
                else
                    let _, r = Division.Univariate.udiv u v
                    if isZeroPolynomial r then
                        Const Zero
                    else
                        let s = totalDegree r
                        let l = leadingCoeff v
                        
                        ((Const -1) ** (m * n)) * (l ** (m - s)) * loop v r

            loop p1 p2

        /// Calculate the discriminant of the given univariate polynomial.
        let public discriminant (p: Polynomial) =
            if not (isUnivariate p) then raise (NotUnivariatePolynomialException p)

            match totalDegree p with
            | n when n <= 1 ->
                // 1 by "convention".
                Const One
            | 2 ->
                let [ a; b; c ] = completeCoefficients p
                // b² - 4ac
                b ** 2 - 4 * a * c
            | 3 ->
                let [ a; b; c; d ] = completeCoefficients p
                // b²c² - 4ac³ - 4b³d - 27a²d² + 18abcd
                (b ** 2) * (c ** 2) - (4 * a * c ** 3) - (4 * b ** 3 * d) - (27 * a ** 2 * d ** 2) + (18 * a * b * c * d)
            | n ->
                let variable, _ = getUnivariateVariableAndIndex p
                let p' = Calculus.derive p variable
                let s = pown -1 (n * (n - 1) / 2)

                // (-1)ⁿ⁽ⁿ⁻¹⁾½ / pₙ ⋅ Resᵥₐᵣ(p, p')
                ((Const s) * resultant p p') / leadingCoeff p

    module public GroebnerBasis =
        open Division.Multivariate

        /// Returns the S-polynomial (*substraction*-polynomial) of the two given polynomials.
        /// See https://en.wikipedia.org/wiki/Gr%C3%B6bner_basis#S-polynomial.
        let private spolynomial (p1: Polynomial) (p2: Polynomial) =
            let α = multiDegree p1
            let β = multiDegree p2
            let γ = Const One, List.map2 max α β

            let lt1 = leadingTerm p1
            let lt2 = leadingTerm p2

            let (Some m1) = γ /? lt1
            let (Some m2) = γ /? lt2

            simplifyCoefficients (p1 * m1 - p2 * m2)

        /// Implement naive Buchberger's algorithm to calculate the Gröbner basis associated with the ideal
        /// generated by the given list of polynomials. The resulting Gröbner basis is not reduced.
        /// See https://en.wikipedia.org/wiki/Buchberger%27s_algorithm.
        /// Our implementation is based on http://www.scholarpedia.org/article/Buchberger%27s_algorithm.
        let public buchberger (polynomials: Polynomial list) =
            let result = HashSet (compatibles polynomials)
            let pairs = Queue [| for f in result do for g in result do if f <> g then (f, g) |]

            while pairs.Count > 0 do
                let (f, g) = pairs.Dequeue()
                let { remainder = r } = reduce (spolynomial f g) (Seq.toList result)

                if not (isZeroPolynomial r) then
                    for p in result do
                        pairs.Enqueue(p, r)

                    result.Add r |> ignore

            Seq.toList result

        /// Given a Gröbner basis, return its equivalent minimal and reduced basis.
        let private reducedGroebnerBasis (polynomials: Polynomial list) =
            let mutable polynomials = List.distinct (List.map normalize polynomials)

            /// Returns the list of polynomials' leading terms for which `p` has been removed.
            let inline leadingTermsWithout p =
                List.choose (fun f -> if p = f then None else Some(leadingTerm f)) polynomials

            let mutable i = 0

            // Make the Gröbner basis minimal
            for p in polynomials do
                let ltps = leadingTermsWithout p

                if List.any ltps (isDivisibleBy (leadingTerm p)) then
                    polynomials <- List.removeAt i polynomials
                else
                    i <- i + 1

            i <- 0

            // Make the Gröbner basis reduced
            for p in polynomials do
                let ltps = leadingTermsWithout p
                let pms = getMonomials p

                if List.any ltps (( = ) >> List.any pms) then
                    polynomials <- List.removeAt i polynomials
                else
                    i <- i + 1

            List.map simplifyCoefficients polynomials

        /// Compute the minimal and reduced Gröbner basis for the given ideal (modeled by a list of equivalent polynomials
        /// whose K-field is delegated to the SumPow representation) using the `currentOrdering` monomial order.
        let public computeGroebnerBasis = compatibles >> buchberger >> reducedGroebnerBasis

    module public Factorization =
        open PureConstantExpression
        open Division.Univariate

        /// Check that the given polynomial is an univariate polynomial whose leading coefficient is 1.
        let inline private isMonic (p: Polynomial) =
            isUnivariate p && Misc.isOne (leadingCoeff p)

        /// Returns the polynomial whose coefficients have been factored by the largest integer common to all coefficients.
        let private coefficientFactoring (p: Polynomial) =
            let coefficients = List.map snd (Map.toList p.polynomial)

            let rec inner resultingGcd =
                function
                | [] -> resultingGcd
                | PureConstantExpressionInteger icoeff :: rest -> inner (intGCD icoeff resultingGcd) rest
                | _ :: rest -> inner resultingGcd rest

            match inner 0 coefficients with
            | 0 | 1 -> Constant 1, p
            | gcd ->
                let coefficients' = List.map (fun coeff -> Simplification.expandAndSimplify (coeff / gcd)) coefficients
                gcd, { p with polynomial = Map.ofList (List.map2 tuple2 (Seq.toList p.polynomial.Keys) coefficients') }

        /// Returns the polynomial whose each term have been factored by the largest monomial & coeff' common to all terms.
        let private termFactoring (p: Polynomial) =
            let monomials = getMonomials p

            let rec inner resultingGcd =
                function
                | [] -> resultingGcd
                | monomial :: rest ->
                    match fst monomial, fst resultingGcd with
                    | PureConstantExpressionInteger icoeff1, PureConstantExpressionInteger icoeff2 ->

                        // The coefficient of `monomialGcd` is 1 (because the monomial part is the variable product part)

                        let icoeff = intGCD icoeff1 icoeff2
                        inner (SumPow.Const icoeff, snd (monomialGCD monomial resultingGcd)) rest

                    | _ ->
                        inner (fst resultingGcd, snd (monomialGCD monomial resultingGcd)) rest

            let gcd = inner (List.min monomials) monomials
            fromMonomials [ gcd ], fromMonomials (List.map (fun m -> Option.get (m /? gcd)) monomials) |> simplifyCoefficients

        /// Returns the polynomial whose each term have been factored by the largest monomial & coeff' common to all terms
        /// with respect to the given variable. This is the most complete term-factoring function.
        let private termFactoringWithRespectTo (p: Polynomial) (variable: Variable) =
            if not (List.contains variable p.variables) then
                raise (PolynomialNotContainsVariablesException (p, [ variable ]))

            let ifactor, p = coefficientFactoring p
            let mfactor, p = termFactoring p
            let factor = SumPow.Const ifactor * mfactor
            let p = asUnivariate variable p

            factor, p

        module private SquareFree =

            /// Determines whether the given univariate polynomial is square free or not.
            let public isSquareFree (p: Polynomial) =
                if not (isUnivariate p) then
                    false
                else // Only defined for univariate polynomials.
                    let variable, _ = getUnivariateVariableAndIndex p
                    isOnePolynomial (Division.polynomialGCD p (Calculus.derive p variable))

            /// Implements the Yun's algorithm for univariate square-free factorization. The return is a polynomial list with
            /// associated exponent. For example, g(x) = x⁴ + 7x³ + 18x² + 20x + 8 ≡ (x + 1)¹(x + 2)³.
            let public squareFreeFactoring (p: Polynomial) =
                if not (isUnivariate p) then
                    raise (NotUnivariatePolynomialException p)

                // If the polynomial is already square-free, then square-free factorization is not necessary.
                if isSquareFree p then [ p, 1 ] else
                let variable, varIndex = getUnivariateVariableAndIndex p

                /// Implements https://en.wikipedia.org/wiki/Square-free_polynomial#Yun's_algorithm.
                let rec yun bi di =
                    if totalDegree bi <= 0 then [] else
                    let ai = Division.polynomialGCD bi di
                    let bi1 = exactDivision bi ai varIndex
                    let ci1 = exactDivision di ai varIndex
                    let di1 = ci1 - Calculus.derive bi1 variable
                    ai :: yun bi1 di1

                let p' = Calculus.derive p variable
                let a0 = Division.polynomialGCD p p'
                let b1 = exactDivision p a0 varIndex
                let c1 = exactDivision p' a0 varIndex
                let d1 = c1 - Calculus.derive b1 variable

                // Units are trivial factors.
                let result = List.filter (not << isOnePolynomial) (yun b1 d1)
                let result = List.map simplifyCoefficients result

                /// Gets the number of times the given polynomial `f` divides the original polynomial, giving `f`'s multiplicity.
                let rec associatedExponent (f: Polynomial) (expn: int) =
                    let f' = f ** expn
                    if totalDegree f' > totalDegree p then
                        expn - 1
                    else
                        let _, r = udiv p f'
                        if isZeroPolynomial r then
                            associatedExponent f (expn + 1)
                        else
                            expn - 1

                List.map (fun a -> a, associatedExponent a 1) result

        [<RequireQualifiedAccess>]
        module public IntegerCoefficients =

            [<RequireQualifiedAccess>]
            module public RationalRoots =

                let inline private rational (num: int, den: int) =
                    let inline fixSign a b = if sign b > 0 then (a, b) else (-a, -b)
                    let g = intGCD num den
                    fixSign (num / g) (den / g)

                let inline private radd (a: int, b: int) (c: int, d: int) = rational (a * d + b * c, b * d)
                let inline private rmul (a: int, b: int) (c: int, d: int) = rational (a * c, b * d)

                let inline private evaluate (p: Polynomial) (x: int * int) =
                    if not (isUnivariate p) then raise (NotUnivariatePolynomialException p)
                    if not (hasIntegerCoefficients p) then raise (PolynomialHaveNonIntegerCoefficientsException p)

                    let st :: coefficients = integerCoefficients p
                    let coefficients = Array.map (fun c -> c, 1) (List.toArray coefficients)

                    Array.fold (fun acc coeff -> radd (rmul acc x) coeff) (st, 1) coefficients

                let inline private isRationalRoot (p: Polynomial) (root: int * int) =
                    if not (isUnivariate p) then raise (NotUnivariatePolynomialException p)
                    if not (hasIntegerCoefficients p) then raise (PolynomialHaveNonIntegerCoefficientsException p)

                    evaluate p root = (0, 1)

                let private getDivisors (x: int) =
                    seq { 1 .. isqrt x }
                    |> Seq.collect
                        (fun i ->
                            if x % i = 0 then
                                let d = x / i
                                if i <> d then [ i; d ] else [ i ]
                            else List.empty)

                let private tryFindRationalRoot (p: Polynomial) =
                    if not (isUnivariate p) then raise (NotUnivariatePolynomialException p)
                    if not (hasIntegerCoefficients p) then raise (PolynomialHaveNonIntegerCoefficientsException p)

                    let coefficients = integerCoefficients p

                    let leadCoeff = List.head coefficients
                    let leastCoeff = List.last coefficients

                    let candidates =
                        seq {
                            for num in getDivisors (abs leastCoeff) do
                                for den in getDivisors (abs leadCoeff) do
                                    yield (-num, den)
                                    yield (+num, den) }

                    Seq.tryFind (isRationalRoot p) candidates

                let private rationalRootFactoring (p: Polynomial) (root: int * int) =
                    if not (isUnivariate p) then raise (NotUnivariatePolynomialException p)
                    if not (hasIntegerCoefficients p) then raise (PolynomialHaveNonIntegerCoefficientsException p)

                    let variable, _ = getUnivariateVariableAndIndex p
                    let (leading :: rcoefficients) = List.map (fun c -> c, 1) (integerCoefficients p)

                    let rec loop last result =
                        function
                        | [] -> result
                        | c :: cs ->
                            let r = radd c (rmul root last)
                            loop r (r :: result) cs
                    
                    let result =
                        loop leading [ leading ] rcoefficients
                        |> List.tail
                        |> List.rev
                        |> List.map (fun (num, den) -> SumPow.Const num / SumPow.Const den)
                    
                    let l = List.length result - 1

                    let p1 =
                        { variables = [ variable ]
                          polynomial =
                            Map.ofList [ (MonomialDegree [ 1 ], SumPow.Const One)
                                         (MonomialDegree [ 0 ], -SumPow.Const (double (fst root)) / SumPow.Const (double (snd root))) ]
                          excludedVariables = p.excludedVariables }

                    let p2 =
                        { variables = [ variable ]
                          polynomial = Map.ofList (List.mapi (fun deg coeff -> MonomialDegree [ l - deg ], coeff) result)
                          excludedVariables = p.excludedVariables }

                    p1, p2

                let private tryFactoring1 (p: Polynomial) =
                    if not (isUnivariate p) then raise (NotUnivariatePolynomialException p)
                    if not (hasIntegerCoefficients p) then raise (PolynomialHaveNonIntegerCoefficientsException p)

                    Option.map (rationalRootFactoring p) (tryFindRationalRoot p)

                let public tryFactoring (p: Polynomial) =
                    if not (isUnivariate p) then raise (NotUnivariatePolynomialException p)
                    if not (hasIntegerCoefficients p) then raise (PolynomialHaveNonIntegerCoefficientsException p)

                    let rec inner p result =
                        match tryFactoring1 p with
                        | None -> Map.addOrUpdate p 1 result (( + ) 1)
                        | Some (u, v) ->
                            let result = Map.addOrUpdate u 1 result (( + ) 1)
                            inner v result

                    match Map.toList (inner p Map.empty) with
                    | [] -> None
                    | [ x, 1 ] when p = x -> None
                    | xs ->
                        let xs = List.filter (not << isOnePolynomial << fst) xs
                        Some (List.map (fun (p, deg) -> simplifyCoefficients p, deg) xs)

            [<RequireQualifiedAccess>]
            module public ComplexRoots =
                // http://www.jonblakely.com/wp-content/uploads/14_2v2.pdf
                ()

            [<RequireQualifiedAccess>]
            module public BerlekampZassenhaus =
                open SquareFree
                // https://github.com/gilith/factor/blob/02a9c1c1a7bee19fa9ebbff852659d9a6ca8678d/src/Factor/Bz.hs



                let public isIrreductible (p: Polynomial) =
                    if not (hasIntegerCoefficients p) then raise (PolynomialHaveNonIntegerCoefficientsException p)

                    PrimitiveAndContent.isPrimitive p && isSquareFree p

        [<RequireQualifiedAccess>]
        module public Specific =

            /// If possible, apply the quadratic formula factorization for the given univariate polynomial.
            let public tryQuadraticFormula (p: Polynomial) =
                if not (isUnivariate p) then raise (NotUnivariatePolynomialException p)

                let variable, _ = getUnivariateVariableAndIndex p
                let coefficients = completeCoefficients p

                if List.length coefficients = 3 then
                    let [ a; b; c ] = coefficients
                    let Δ2 = Fun("Sqrt",  [b ** 2 - 4 * a * c]) |> Simplification.simplify
                    let r1 = (-b + Δ2) / (2 * a) |> Simplification.simplify
                    let r2 = (-b - Δ2) / (2 * a) |> Simplification.simplify

                    let a = fromCoefficients [ variable ] [ 1 ] [ SumPow.Const One; -r1 ]
                    let b = fromCoefficients [ variable ] [ 1 ] [ SumPow.Const One; -r2 ]

                    Some [ (a, 1); (b, 1) ] // returns a¹*b¹
                else
                    None

            /// If possible, complete the square of the given univariate polynomial.
            let public tryCompleteTheSquare (p: Polynomial) =
                if not (isUnivariate p) then raise (NotUnivariatePolynomialException p)

                let variable, _ = getUnivariateVariableAndIndex p
                let coefficients = completeCoefficients p
                
                if List.length coefficients = 3 then
                    let [ a; b; c ] = coefficients
                    if Misc.isZero b then None
                    else
                        let _, b, c = SumPow.Const One, (b / a), (c / a)

                        let p = fromCoefficients [ variable ] [ 1 ] [ SumPow.Const One; b / 2 ]
                        let c = fromCoefficients [ variable ] [ 0 ] [ c - (b ** 2) / 4 ]

                        Some [ (c, 1); (p, 2) ] // returns c¹p²
                else
                    None

            /// If possible, apply the Sophie Germain's identity for the given univariate polynomial.
            let public trySophieGermain (p: Polynomial) =
                if not (isUnivariate p) then raise (NotUnivariatePolynomialException p)
                if not (isMonic p) then None else

                let variable, _ = getUnivariateVariableAndIndex p
                let coefficients = completeCoefficients p

                if List.length coefficients = 5 then
                    let [ _; b; c; d; e ] = coefficients
                    if not (List.forall Misc.isZero [ b; c; d ]) then None else

                    let t = Simplification.simplify (Fun("Root", [ e / 4; SumPow.Const 4 ]))
                    let q1 = Simplification.simplify (2 * t)
                    let q2 = Simplification.simplify (2 * (t ** 2))

                    let a = fromCoefficients [ variable ] [ 2 ] [ SumPow.Const One; -q1; q2 ]
                    let b = fromCoefficients [ variable ] [ 2 ] [ SumPow.Const One;  q1; q2 ]

                    Some [ (a, 1); (b, 1) ] // returns a¹*b¹
                else
                    None

        /// 
        let inline private subUnivPolynomiams (p: Polynomial) =
            if not (isUnivariate p) then raise (NotUnivariatePolynomialException p)

            let coefficients = completeCoefficients p
            let poly = List.mapi (fun d c -> MonomialDegree [ List.length coefficients - d ], c) coefficients
            let sub = List.partition (snd >> Misc.isPureConstInteger) poly
            0

        [<NoEquality; NoComparison; RequireQualifiedAccess>]
        type public FactoringResult =

            /// In the case of a multivariate polynomial without specification of the variables to be forced.
            | Alternatives of (Polynomial * Polynomial) seq

            /// The polynomial is factored as the product of several powers of polynomials.
            | Univariate of (Polynomial * int) list

            /// The polynomial was unable to be factored.
            | Nothing

        let inline private trySpecific (p: Polynomial) =
            None |> Option.orElseWith (konst (Specific.tryQuadraticFormula p))
              // |> Option.orElseWith (konst (Specific.tryCompleteTheSquare p)) // Not a factorized form!
                 |> Option.orElseWith (konst (Specific.trySophieGermain p))

        let inline private tryIntCoeff (p: Polynomial) =
            if hasIntegerCoefficients p
            then IntegerCoefficients.RationalRoots.tryFactoring p
            else None

        let inline private initialFactoring (p: Polynomial) =
            let p1, p2 = termFactoringWithRespectTo p p.variables.Head
            (p1, 1) :: SquareFree.squareFreeFactoring p2

        let rec private factor1 (p: Polynomial) =
            if totalDegree p = 1 then [ p, 1 ] else

            let onep = fromCoefficients [ p.variables.Head ] [ 0 ] [ SumPow.Const One ]
            let mutable result = []

            let inline distributePower d = List.map (fun (p', d') -> (p', d * d'))

            for (p, d) in initialFactoring p do
                // If the polynomial consists of a single term, then it might not be factored.
                if Map.count p.polynomial = 1 then result <- (p, d) :: result else

                match tryIntCoeff p with
                | None ->
                    match trySpecific p with
                    | None -> result <- (p, d) :: result
                    | Some res -> result <- distributePower d res @ result
                | Some res ->
                    let res = distributePower d res
                    let res = List.map (fun (p, d) -> distributePower d (factor1 p)) res
                    let res = List.flatten res
                    result <- res @ result

            result |> List.filter (fun (p, _) -> p <> onep)

        let public tryFactoring (p: Polynomial) (variable: Variable option) =
            if Option.isSome variable && not (List.contains variable.Value p.variables) then
                raise (PolynomialNotContainsVariablesException (p, [ variable.Value ]))

            if isMultivariate p && Option.isNone variable
            then FactoringResult.Alternatives (Seq.map (termFactoringWithRespectTo p) p.variables)
            else FactoringResult.Univariate (factor1 p)

        let public showFactoringResult =
            function
            | FactoringResult.Nothing -> @"\text{Nothing}"

            | FactoringResult.Alternatives alternatives ->
                let alternatives = Seq.toList alternatives
                sprintf @"\begin{align*} %s \end{align*}"
                        (System.String.Join(@"\\", List.map (fun (c, p) -> sprintf @"%s\cdot\left(%s\right)" (toLatexValue c) (toLatexValue p)) alternatives))

            | FactoringResult.Univariate ps ->
                System.String.Join(@" \cdot ",
                    List.map (fun (p, d) -> sprintf @"\left(%s\right)^%d" (toLatexValue p) d) ps)

    module public Interpolation =

        /// Fast approximation of the value of `f(x)` using polynomial interpolation. If `x` is numeric, then the result
        /// will be a constant. Otherwise, the result will be a univariate polynomial in the variable `x`.
        let public newtonUnivariatePolynomialInterpolation (points: (SumPow * SumPow) array) (x: SumPow) =
            let xdata, ydata = Array.unzip points

            let coefficients =
                let l = Array.length xdata
                let mutable result = ydata

                for k in 1 .. l - 1 do
                    for i in k .. l - 1 do
                        result.[i] <- (result.[i] - result.[k - 1]) / (xdata.[i] - xdata.[k - 1])

                result
            
            let degree = Array.length points - 1
            let mutable result = coefficients.[degree]

            for k in 1 .. degree do
                result <- coefficients.[degree - k] + (x - xdata.[degree - k]) * result

            match result with
            | PureConstantExpression.PureConstantExpression pc -> SumPow.Const (NumericEvaluation.evaluate0 pc)
            | result -> result

    module public NumericEvaluation =
        open System.Numerics

        exception public NegativeNumberOfIterationsException of int
        exception public NegativeToleranceException of double

        let inline private complexf (x: double) = System.Numerics.Complex.op_Implicit x

        /// Representation of a purely numerical univariate polynomial as an array of (degree, coefficient).
        type public NumericUnivariatePolynomial = (int * Complex) array

        /// An active pattern which match a purely numerical univariate polynomial.
        let public (|NumericUnivariatePolynomial|_|) (p: Polynomial) : NumericUnivariatePolynomial option =
            if not (isUnivariate p) then None else

            let poly = Map.toArray p.polynomial

            if not (Array.forall Misc.isPureConst (Array.map snd poly)) then None else

            let inline mapper (MonomialDegree deg, coeff) =
                deg.[0], complexf (toDouble (NumericEvaluation.evaluate0 coeff))

            Some (Array.map mapper poly)

        /// Converts the given univariate polynomial into a purely numerical univariate polynomial, if possible.
        let public tryNumericUnivariatePolynomial =
            function
            | NumericUnivariatePolynomial nup -> Some nup
            | _ -> None

        let private completeNumericUnivariatePolynomial (nup: NumericUnivariatePolynomial) =
            let deg = fst (Array.maxBy fst nup)

            [| for i = deg downto 0 do
                (i, Array.tryFind (fst >> ( = ) i) nup
                    |> Option.map snd
                    |> Option.defaultValue 0) |]

        let private fromCoefficients (coefficients: Complex array) =
            Array.mapi (fun deg coeff -> (deg, coeff)) (Array.rev coefficients)

        let private normalize (nup: NumericUnivariatePolynomial) =
            let lc = snd (Array.maxBy fst nup)
            Array.map (fun (deg, coeff) -> (deg, coeff / lc)) nup

        let private derive (nup: NumericUnivariatePolynomial) =
               Array.map (fun (deg, coeff) -> (deg - 1, coeff * double deg)) nup
            |> Array.filter (fun x -> fst x >= 0)

        /// Evaluates the given numerical univariate polynomial to the given value.
        let inline public evaluate (nup: NumericUnivariatePolynomial) (value: Complex) =
            Array.fold (fun acc (deg, coeff) -> acc + (value ** double deg) * coeff) (complexf 0.0) nup

        /// Implements the Newton-Raphson method to find a root close to the given initial point of the given
        /// numerical univariate polynomial.
        let public newtonRaphson (initial: Complex) (eps: double) (maxIterations: int) (nup: NumericUnivariatePolynomial) =
            if maxIterations < 0 then raise (NegativeNumberOfIterationsException maxIterations)
            if eps < 0 then raise (NegativeToleranceException eps)

            let derivated = derive nup

            let rec next (x0: Complex) (k: int) =
                let x1 = x0 - (evaluate nup x0 / evaluate derivated x0)
                let err = Complex.Abs (x1 - x0)

                if err <= eps || k = maxIterations then x0 else next x1 (k + 1)

            next initial 0

        /// Round the given numerical value to the given tolerance.
        let private roundUpToTolerance (eps: double) (value: Complex) =
            let n = decimalCount eps
            if n <= 0 || n > 15 then value else

            let re = Math.Round(value.Real, n)
            let im = Math.Round(value.Imaginary, n)

            let re = if abs re = 0 then 0.0 else re
            let im = if abs im = 0 then 0.0 else im

            Complex(re, im)

        /// Implement the Durand–Kerner method to find all the roots of the given numerical univariate polynomial.
        /// This method is not generally convergent.
        /// See https://en.wikipedia.org/wiki/Durand%E2%80%93Kerner_method.
        let public findRoots (nup: NumericUnivariatePolynomial) (eps: double) (maxIterations: int) =
            if maxIterations < 0 then raise (NegativeNumberOfIterationsException maxIterations)
            if eps < 0 then raise (NegativeToleranceException eps)

            let nup = completeNumericUnivariatePolynomial (normalize nup)
            let n = Array.length nup - 1

            let inline init i =
                Complex.FromPolarCoordinates(1.0, 2.0 * Math.PI * double i / double n)

            let mutable roots = Array.init n init
            let mutable converged = false
            let mutable iter = 0

            while not converged && iter < maxIterations do
                converged <- true

                for i in 0 .. n - 1 do
                    let oldRoot = roots.[i]
                    let numerator = evaluate nup oldRoot
                    let mutable denominator = Complex.One

                    for j in 0 .. n - 1 do
                        if i <> j then
                            denominator <- denominator * (oldRoot - roots.[j])

                    let newRoot = oldRoot - (numerator / denominator)

                    if Complex.Abs(newRoot - oldRoot) > eps then
                        converged <- false

                    roots.[i] <- newRoot
                iter <- iter + 1

            if converged
            then Some (Array.map (roundUpToTolerance eps) roots)
            else None

        /// Use the Durand–Kerner method to find all the real roots of the given numerical univariate polynomial.
        /// This method is not generally convergent.
        /// See https://en.wikipedia.org/wiki/Durand%E2%80%93Kerner_method.
        let public realRoots (nup: NumericUnivariatePolynomial) (eps: double) (maxIterations: int) =
            match findRoots nup eps maxIterations with
            | None -> None
            | Some roots ->
                let inline predicate (root: Complex) = approximatelyEquals (abs root.Imaginary) 0.0 (ValueSome eps)
                let result = Array.filter predicate roots

                if Array.isEmpty result then None else
                Some (Array.map (fun (root: Complex) -> root.Real) result)

    /// Some predefined polynomials expressions.
    [<RequireQualifiedAccess>]
    module public Prefab =

        // Define the following polynomials:
        //  - Falling and rising factorial polynomials ;
        //  - Bessel and reversed Bessel polynomials ;
        //  - Chebyshev of first and second kind polynomials ;
        //  - Hermite (Physicist and Probabilist conventions) polynomials ;
        //  - Laguerre polynomials ;

        exception public InvalidChebyshevKindException of int

        [<Struct; RequireQualifiedAccess; NoEquality; NoComparison>]
        type public FallingOrRising =
            | Falling   // x(x - 1)(x - 2) ... (x - n + 1)
            | Rising    // x(x + 1)(x + 2) ... (x + n - 1)

        /// Generates the falling and rising factorials.
        /// See https://en.wikipedia.org/wiki/Falling_and_rising_factorials.
        let public factorial (variable: Variable) (order: int) (kind: FallingOrRising) =
            match order with
            | 0 -> zeroPolynomial [ variable ]
            | 1 -> fromCoefficients [ variable ] [ 1 ] [ Const One ]
            | n ->
                let inline op k =
                    match kind with
                    | FallingOrRising.Falling -> variable - Const k
                    | FallingOrRising.Rising -> variable + Const k

                [| 0 .. n - 1 |]
                |> Array.fold (fun acc k -> acc * op k) (Const One)
                |> asUnivariatePolynomial variable []   // slow
                |> fst

        /// Generates the Bessel polynomial.
        /// See https://en.wikipedia.org/wiki/Bessel_polynomials.
        let public bessel (variable: Variable) (order: int) =
            let coefficients =
                [ for k = order downto 0 do
                    let num0 = Const (fromBigInt (ifactorial (order + k)))
                    let den1 = Const (fromBigInt (ifactorial (order - k)))
                    let den2 = Const (fromBigInt (ifactorial k))
                    let den3 = Const 2 ** Const (fromBigInt k)
                    let den0 = den1 * den2 * den3
                    Simplification.simplify (num0 / den0) ]

            fromCoefficients [ variable ] [ order ] coefficients

        /// Generates the reversed Bessel polynomial.
        /// See https://en.wikipedia.org/wiki/Bessel_polynomials.
        let public reversedBessel (variable: Variable) (order: int) =
            reciprocalPolynomial (bessel variable order)

        /// Generates the Chebyshev polynomial of the `kind` (1 or 2) kind.
        /// See https://en.wikipedia.org/wiki/Chebyshev_polynomials.
        let private chebyshev (variable: Variable) (order: int) (kind: int) =
            if (kind <> 1 && kind <> 2) then
                raise (InvalidChebyshevKindException kind)

            // Definition by recurrence relation
            let loop n =
                let rec loopAux n prev curr =
                    match n with
                    | 0 -> prev
                    | n -> loopAux (n - 1) curr (2 * variable * curr - prev)
                loopAux n (Const One) (kind * variable)

            loop order
            |> asUnivariatePolynomial variable []   // slow
            |> fst

        /// Generates the Chebyshev polynomial of the first kind.
        /// See https://en.wikipedia.org/wiki/Chebyshev_polynomials.
        let public chebyshev1 (variable: Variable) (order: int) =
            chebyshev variable order 1

        /// Generates the Chebyshev polynomial of the second kind.
        /// See https://en.wikipedia.org/wiki/Chebyshev_polynomials.
        let public chebyshev2 (variable: Variable) (order: int) =
            chebyshev variable order 2

        [<Struct; RequireQualifiedAccess; NoEquality; NoComparison>]
        type private HermiteConvention =
            | Physicist
            | Probabilist

        /// Generate the Hermite polynomial of order `order` and following the given convention.
        /// See https://en.wikipedia.org/wiki/Hermite_polynomials.
        let private hermite (variable: Variable) (order: int) (convention: HermiteConvention) =
            let coeffs = Array.init (order + 1) (fun _ -> Array.zeroCreate (order + 1))
            
            let convFactor =
                match convention with
                | HermiteConvention.Physicist -> 2I
                | HermiteConvention.Probabilist -> 1I

            coeffs.[0].[0] <- 1I

            if order > 0 then
                coeffs.[1].[1] <- convFactor

            for i in 1 .. (order - 1) do
                for k in 0 .. (i + 1) do
                    let coeff1 = if k > 0 then convFactor * coeffs.[i].[k - 1] else 0I
                    let coeff2 = if k <= i then convFactor * bigint i * coeffs.[i - 1].[k] else 0I
                    coeffs.[i + 1].[k] <- coeff1 - coeff2

            let coefficients =
                List.ofArray (Array.map (fromBigInt >> Const) (Array.rev coeffs.[order]))

            fromCoefficients [ variable ] [ order ] coefficients

        /// Generate the Hermite polynomial of order `order` and following the physicist convention.
        /// See https://en.wikipedia.org/wiki/Hermite_polynomials.
        let public physicistHermite (variable: Variable) (order: int) =
            hermite variable order (HermiteConvention.Physicist)

        /// Generate the Hermite polynomial of order `order` and following the probabilist convention.
        /// See https://en.wikipedia.org/wiki/Hermite_polynomials.
        let public probabilistHermite (variable: Variable) (order: int) =
            hermite variable order (HermiteConvention.Probabilist)

        /// Generate the closed-form Laguerre polynomial of order `order`.
        /// See https://en.wikipedia.org/wiki/Laguerre_polynomials.
        let public laguerre (variable: Variable) (order: int) =
            let coefficients =
                [ for k = order downto 0 do
                    let num = (pown -1 k) * (binomial order k)
                    let den = ifactorial k
                    Simplification.simpPureConst (Const num / Const (fromBigInt den)) ]

            fromCoefficients [ variable ] [ order ] coefficients

        /// Generates a random multivariate polynomial for testing or debugging purpose.
        let public generateRandom (n: int) (variables: string list) =
            let vs = List.map Name variables
            let rnd = Random()

            List.init n (fun _ ->
                Term
                    [ powId (Const(rnd.Next(1, n)))
                      Pow(vs.[rnd.Next(0, vs.Length)], Const(rnd.Next(1, n))) ])
            |> Sum
            |> asMultivariatePolynomial vs []
            |> fst
