namespace Liyh.Kernel.Polynomial

module rec Univariate =
    open System
    open System.Collections.Generic
    open System.Linq
    open Liyh.Kernel.SumProd

    /// Hash the given monomial.
    let private hashMonomial { coefficient = coeff; exponent = expn } =
        HashCode.Combine(coeff, expn)

    /// Implements the equality of SumProd expressions.
    let rec private equalsMonomials (mono: Monomial) (sp2: obj) =
        match sp2 with
        | :? Monomial as { coefficient = coeff; exponent = expn } ->
            mono.coefficient = coeff && mono.exponent = expn
        | _ -> false

    /// Represents a monomial.
    [<Struct; CustomEquality; NoComparison>]
    type public Monomial =
        { coefficient: SumProd
          exponent: int }

        override this.GetHashCode () = hashMonomial this
        override this.Equals arg = equalsMonomials this arg

    /// Build a monomial from the given coefficient and exponent.
    let inline public monomial coeff expn =
        { coefficient = coeff
          exponent = expn }

    /// Returns the polynomial ordored.
    let inline private ordered (p: Monomial list) =
        p.OrderByDescending(fun k -> k.exponent) |> Seq.toList

    /// Checks if the given polynomial is ordored.
    let inline private isOrdered (p: Monomial list) =
        (p.Zip (p.Skip(1), fun a b -> a, b)).All(fun (a, b) -> a.exponent > b.exponent)

    ///Checks if the given polynomial is dense.
    let private isDense (p: Monomial list) =
        p.Head.exponent = p.Length

    /// Checks if the given polynomial is sparse.
    let private isSparse = isDense >> not

    /// Returns the number of zero coefficients of the polynomial.
    let private sparsity (p: Monomial list) =
        degree p - p.Length

    /// Gets the degree of the polynomial.
    let private degree (p: Monomial list) =
        if List.isEmpty p then 0
        else (List.maxBy (fun mono -> mono.exponent) p).exponent

    /// Gets the list of coefficients assuming they are integers.
    let inline private getCoefficients (p: Monomial list) =
        List.map (fun mono -> mono.coefficient) p

    /// Apply the given function to each coefficiens of the given polynomial.
    let private mapCoefficients (f: SumProd -> SumProd) =
        List.map (fun { coefficient = coeff; exponent = expn } -> monomial (f coeff) expn)

    /// Gets the list of coefficients assuming they are integers.
    let private getIntegerCoefficients (p: Monomial list) =
        List.map
            (function
             | { coefficient = Integer x } -> x
             | { coefficient = x } -> raise (NotABigIntException x)) p

    /// Gets the list of coefficients assuming they are floats.
    let private getFloatCoefficients (p: Monomial list) =
        List.map
            (function
             | { coefficient = Float x } -> x
             | { coefficient = x } -> raise (NotAFloatException x)) p

    /// Gets the list of coefficients assuming they are numerical (integer or float).
    let private getNumericCoefficients (p: Monomial list) =
        List.map
            (function
             | { coefficient = Integer x } -> float x
             | { coefficient = Float x } -> x
             | { coefficient = x } -> raise (NotAFloatException x)) p

    /// Gets the list of exponents of the given polynomial.
    let inline private getExponents (p: Monomial list) =
        List.map (fun mono -> mono.exponent) p

    /// Generates a list of monomials from the given predicate.
    let private create (pred: int -> SumProd) (degree: int) =
        assert (degree >= 0)
        [ for i = 0 to degree do monomial (pred i) (degree - i) ]

    /// Generates a polynomial of degree `degree` from the given predicate.
    let public generate (pred: int -> SumProd) (degree: int) (variable: SumProd) =
        Polynomial(variable, create pred degree)

    /// Returns the polynomial without the zero coefficients.
    let private sparsePolynomial (p: Monomial list) =
        List.filter (fun mono -> mono.coefficient <> Zero) p

    /// Returns the complete polynomial.
    let private densePolynomial (p: Monomial list) =
        assert (isOrdered p)

        let exponents = getExponents p
        let mutable j = 0

        [ for i = exponents.Head downto 0 do
              if j <= exponents.Length - 1 && exponents.[j] = i
              then yield p.[j]; j <- j + 1
              else yield monomial Zero i ]

    /// Evaluates the integer polynomial in O(n) time with the given value.
    let inline private hornerMethodInteger (xs: bigint list) (value: bigint) =
        List.reduce (fun acc x -> acc * value + x) xs

    /// Evaluates the float polynomial in O(n) time with the given value.
    let inline private hornerMethodFloat (xs: float list) (value: float) =
        List.reduce (fun acc x -> acc * value + x) xs

    /// Evaluate the polynomial with the given value.
    let private evaluate (p: Monomial list) (variable: SumProd) (value: SumProd) =
        
        let inline dummyEval () =
            List.fold
                (fun acc { coefficient = coeff; exponent = expn }
                    -> acc + substitutes variable value (coeff *** Integer (bigint expn))) Zero p

        if not (isOrdered p) || not (hasNumericCoefficients p) || not (isNumeric value)
        then dummyEval ()
        else
            let p = if isDense p then p else densePolynomial p

            match p.Head, value with
            | { coefficient = Integer _ }, Integer value -> hornerMethodInteger (getIntegerCoefficients p) value |> Integer
            | { coefficient = Float _ }, Float value -> hornerMethodFloat (getFloatCoefficients p) value |> Float
            | _, _ -> dummyEval ()

    /// Returns the greatest common divisor of two polynomials.
    let private polynomialGCD (p1: Monomial list) (p2: Monomial list) =
        let rem a b = snd (longDivision a b)

        let p1, p2 =
            (getIntegerCoefficients p1 |> List.map float),
            (getIntegerCoefficients p2 |> List.map float)

        let inner a b =
            let rec inner a b = if b = [] then a else inner b (rem a b)
            let raw = inner a b
            fst (longDivision raw [ List.head raw ])

        inner p1 p2

    /// Performs the long division of the given polynomials (floats), returns the remainder and the quotient.
    let public longDivision (xs: float list) (ys: float list) =

        let rec shift n xs =
            if n <= 0 then xs
            else shift (n - 1) (xs @ [ 0. ])

        let rec pad n xs =
            if n <= 0 then xs
            else pad (n - 1) (0. :: xs)

        let rec norm = function
            | 0. :: xs -> norm xs
            | xs -> xs

        let deg xs = List.length (norm xs) - 1

        let zip op p q =
            let d = List.length p - List.length q
            in List.map2 op (pad -d p) (pad d q)

        let rec inner f s q =
            let degDiff = deg f - deg s

            if degDiff < 0 then q, f
            else
                let k = List.head f / List.head s
                let ks = List.map (( * ) k) (shift degDiff s)

                let q' = zip ( + ) q (shift degDiff [ k ])
                let f' = norm (List.tail (zip ( - ) f ks))

                inner f' s q'

        inner (norm xs) (norm ys) []

    /// Checks whether the given polynomial has only numerical coefficients.
    let private hasNumericCoefficients (p: Monomial list) =
        List.forall (fun mono -> isNumeric mono.coefficient) p

    /// Checks whether the given polynomial has only float coefficients.
    let private hasFloatCoefficients (p: Monomial list) =
        List.forall (fun mono -> isFloat mono.coefficient) p

    /// Checks whether the given polynomial has only integer coefficients.
    let private hasIntegerCoefficients (p: Monomial list) =
        List.forall (fun mono -> isInteger mono.coefficient) p

    /// Returns the nth derivative of the given polynomial.
    let private nthDerivative (nth: int) (p: Monomial list) =
        let inner expn =
            List.reduce ( * ) [ for k = expn downto expn - nth + 1 do k ] |> bigint

        if nth = 0 then p
        elif nth > degree p then [ monomial Zero 0 ]
        else [ for { coefficient = coeff; exponent = expn } in p do
                if expn >= nth then monomial (coeff * Integer (inner expn)) (expn - nth) ]

    /// Returns the first derivative of the given polynomial.
    let private derivative = nthDerivative 1

    /// Returns the reciprocal polynomial.
    let private reciprocal (p: Monomial list) =
        let exponents = getExponents p
        List.mapi (fun i coeff -> monomial coeff exponents.[i]) (List.rev (getCoefficients p))

    /// Check whether the given univariate polynomial is square free.
    let private isSquareFree (p: Monomial list) =
        polynomialGCD p (derivative p) = [ 1. ]

    /// Performs long division of two polynomials, returns the remainder of the division and the quotient.
    let public tryDivision (p1: Monomial list) (p2: Monomial list) =
        if not (hasNumericCoefficients p1 && hasNumericCoefficients p2) then None
        else
            assert (isOrdered p1 && isOrdered p2)

            let coeffs1 = getNumericCoefficients p1
            let coeffs2 = getNumericCoefficients p2

            let remainder, quotient = longDivision coeffs1 coeffs2

            let remainder = List.map asSPNumeric remainder
            let quotient = List.map asSPNumeric quotient

            Some (quotient, remainder)

    /// Addition of polynomials.
    let private addition (p1: Monomial list) (p2: Monomial list) =
        p1 @ p2 |> List.groupBy (fun mono -> mono.exponent)
                |> List.map (fun (deg, xs) -> monomial (List.sumBy (fun mono -> mono.coefficient) xs) deg)
                |> List.filter (fun mono -> mono.coefficient <> Zero)

    /// Substraction of polynomials.
    let private substraction (p1: Monomial list) (p2: Monomial list) =
        addition p1 (mapCoefficients neg p2)

    /// Multiplication of polynomials.
    let private multiplication (p1: Monomial list) (p2: Monomial list) =
        assert (isOrdered p1 && isOrdered p2)

        let p1, p2 = densePolynomial p1, densePolynomial p2
        let m, n = degree p1, degree p2
        let result = List<SumProd>([ for _ = 0 to m + n do yield Zero ])

        for i = 0 to m do
            for j = 0 to n do
                result.[i + j] <- result.[i + j] + (p1.[m - i].coefficient * p2.[n - j].coefficient)

        List.mapi (fun i coeff -> monomial coeff i) (Seq.toList result)

    /// Power of a polynomial.
    let private pow (p1: Monomial list) (expn: int) =
        assert (expn >= 0)

        if expn = 0 then [ monomial Zero 0 ]
        elif expn = 1 then p1
        else List.reduce (ordered >> multiplication) [ for _ = 1 to expn do yield p1 ]

    /// Factorise the given polynomial (using the Cantor-Zassenhaus algorithm)
    let private factorize (p: Monomial list) =
        // petit écureuil
        p

    let private sumprod (variable: SumProd) (p: Monomial list) =
        List.map (fun {coefficient = coeff; exponent = expn} -> coeff * (variable *** Integer (bigint expn))) p
        |> Sum

    /// Construct the polynomial that has the given roots.
    let public fromIntegerRoots (variable: SumProd) (roots: bigint list) =
        let coefficients = List<bigint> [ -roots.Head; 1I ]

        for k = 2 to roots.Length do
            coefficients.Add 1I

            for i = (k - 2) downto 0 do
                coefficients.[i + 1] <- coefficients.[i] - roots.[k - 1] * coefficients.[i + 1]

            coefficients.[0] <- -coefficients.[0] * roots.[k - 1]
            if Math.IEEERemainder(k, 2) = 1 then coefficients.[k] <- -coefficients.[k]

        Polynomial(variable, (Seq.toList >> List.rev) coefficients)

    /// Review the LaTex rendering of the given polynomial.
    let private latex (variable: SumProd) (monomials: Monomial list) =

        let inner { coefficient = coeff; exponent = expn } =
            let coeff = absSP coeff

            let sCoeff =
                if isOne coeff then ""
                elif isNumeric coeff then sprintf "%s" coeff.ToLatex
                else sprintf @"%s\cdot" coeff.ToLatex

            let sTerm =
                if expn = 0 then ""
                elif expn = 1 then variable.ToLatex
                else sprintf @"{%s}^%d" variable.ToLatex expn

            if isZero coeff then ""
            elif expn = 0 then sCoeff
            else sCoeff + sTerm

        let showOp = function
            | { coefficient = Negative _ } -> "-"
            | _ -> "+"

        match monomials with
        | x :: xs -> List.fold (fun acc a -> sprintf "%s %s %s" acc (showOp a) (inner a)) (inner x) xs
        | [] -> ""

    /// Hash polynomials.
    let private hashPolynomial (variable: SumProd) (p: Monomial list) =
        HashCode.Combine(hash variable, List.map hashMonomial p)

    /// Tests the equality of polynomials.
    let private equalsPolynomials (p1: Polynomial) (arg: obj) =

        // Normally, a polynomial will always be ordered by construction, so we do not need to implement any
        // specific equality check as with SumProd.

        match arg with
        | :? Polynomial as p2 -> p1.Variable = p2.Variable
                              && sparsePolynomial p1.Monomials = sparsePolynomial p2.Monomials
        | _ -> false

    /// Approximate the reals roots of the given polynomial.
    let private numericRoots (p: Monomial list) =
        assert (isOrdered p)
        let coefficients = getNumericCoefficients p
        ()

    /// Represents a univariate polynomial.
    type public Polynomial(variable: SumProd, monomials: Monomial list, alreadyOrdored: bool) =
        let monomials =
            if alreadyOrdored then monomials
            else ordered monomials

        new(variable: SumProd, monomials: Monomial list) =
            Polynomial(variable, monomials, false)

        new(variable: SumProd, coefficients: bigint list) =
            let deg = coefficients.Length - 1
            let monomials = create (fun i -> Integer coefficients.[i]) deg
            Polynomial(variable, monomials, true)

        new(variable: SumProd, coefficients: int list) =
            Polynomial(variable, List.map (fun (x: int) -> bigint x) coefficients)

        new(variable: SumProd, coefficients: float list) =
            let deg = coefficients.Length - 1
            let monomials = create (fun i -> asSPNumeric coefficients.[i]) deg
            Polynomial(variable, monomials, true)

        /// Returns the degree of the polynomial.
        member __.Degree = degree monomials

        /// Returns the variable of the polynomial.
        member __.Variable = variable

        /// Returns the monomials of the polynomial.
        member __.Monomials = monomials

        /// Returns the list of coefficients of the polynomial.
        member __.Coefficients = getCoefficients monomials

        /// Evaluate the polynomial with the given value.
        member __.Evaluate = evaluate monomials variable

        /// Returns the nth derivative of the polynomial.
        member __.Derivative n = Polynomial(variable, nthDerivative n monomials)

        /// Returns the LaTex representation of the polynomial.
        member __.ToLatex = latex variable monomials

        /// Returns the sparse representation of the polynomial.
        member __.Sparse = Polynomial(variable, sparsePolynomial monomials, true)

        /// Returns the dense representation of the polynomial.
        member __.Dense = Polynomial(variable, densePolynomial monomials, true)

        /// Returns the reciprocal polynomial.
        member __.Reciprocal = Polynomial(variable, reciprocal monomials, true)

        /// Checks if the polynomial is square free.
        member __.IsSquareFree = isSquareFree monomials

        /// Returns the factorized polynomial.
        member __.Factorize = factorize monomials

        /// Returns all the reals roots of the polynomial.
        member __.NumericRoots = numericRoots monomials

        /// Convert the polynomial into the SumProd data structure.
        member __.SumProd = sumprod variable monomials

        /// Returns a string description of the polynomial.
        member __.Description =
            sprintf @"%s polynomial of degree %d in the variable $%s$"
                (if isDense monomials then "Dense" else "Sparse") (degree monomials) (variable.ToLatex)

        /// Adds the given polnomials.
        static member ( + ) (p1: Polynomial, p2: Polynomial) =
            assert (p1.Variable = p2.Variable)
            Polynomial(p1.Variable, addition p1.Monomials p2.Monomials)

        /// Substracts the given polynomials.
        static member ( - ) (p1: Polynomial, p2: Polynomial) =
            assert (p1.Variable = p2.Variable)
            Polynomial(p1.Variable, substraction p1.Monomials p2.Monomials)

        /// Multiply the given polynomials.
        static member ( * ) (p1: Polynomial, p2: Polynomial) =
            assert (p1.Variable = p2.Variable)
            Polynomial(p1.Variable, multiplication p1.Monomials p2.Monomials)

        /// Raises the polynomial to the given power.
        static member ( *** ) (p1: Polynomial, expn: int) =
            Polynomial(p1.Variable, pow p1.Monomials expn)

        /// Computes the greatest common divisor of the given polynomials.
        static member GCD (p1: Polynomial, p2: Polynomial) =
            assert (p1.Variable = p2.Variable)
            Polynomial(p1.Variable, polynomialGCD p1.Monomials p2.Monomials)

        override this.GetHashCode () = hashPolynomial variable monomials
        override this.Equals arg = equalsPolynomials this arg

// https://github.com/AdamWhiteHat/Polynomial/blob/master/Polynomial/Polynomial.cs

