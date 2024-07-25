namespace Liyh.Kernel

#nowarn "40"

(*

'SumProd' (SP) is a main representation of Liyh for symbolic computations. It implements the calculus
of the field of reals, namely that SP contains the real numbers. It has two operators, addition (+)
and multiplication (.), which have the following properties:

    - Associativity:    A + (B + C) = (A + B) + C
                        A . (B . C) = (A . B) . C

    - Commutativity:    A + B = B + A
                        A . B = B . A

    - Identity:         A + 0 = A
                        A . 1 = A

    - Inverse:          A + (-A) = 0
                        A . (A⁻¹)= 1

    - Distributivity:   A . (B + C) = (A . B) + (A . C)

*)

// il faudrait rendre ça plus simple encore => monoïde => groupe => corps

module rec SumProd =
    open Liyh.Utils
    open System.ComponentModel
    open System.Collections.Generic
    open System.Linq
    open System

    exception public TooBigBigintPower of bigint
    exception public NotAFractionException of SumProd
    exception public NotASumException of SumProd
    exception public NotAConstantLiteralException of SumProd
    exception public NotAFloatException of SumProd
    exception public NotABigIntException of SumProd
    exception public NotNumericException of SumProd
    exception public NotAVariableException of SumProd * SumProd
    exception public NotAProductException of SumProd

    /// Convert a SumProd to a string as a LaTex format.
    let rec private latex (sp: SumProd) =

        let lparens = function
            | Sum _
            | Prod _ as sp -> sprintf @"{\left(%s\right)}" (latex sp)
            | sp -> sprintf @"{%s}" (latex sp)

        let lfold x xs op =
            let inner acc a = sprintf "%s %s %s" acc op (lparens a)
            List.fold inner (latex x) xs

        match sp with
        | Integer x -> string x
        | Float x -> sprintf "%g" x
        | Variable name -> name
        | Frac (a, b) -> sprintf @"\frac{%s}{%s}" (latex a) (latex b)
        | Function (name, []) -> sprintf @"\text{%s}()" name
        | Function (name, x :: xs) -> sprintf @"\text{%s}\left(%s\right)" name (lfold x xs ",")
        | Pow (basis, expn) -> lparens basis + "^" + lparens expn
        | Sum (x :: xs) -> lfold x xs "+"
        | Sum [] -> ""
        | Prod (x :: xs) -> lfold x xs @"\cdot"
        | Prod [] -> ""
        | Infinity -> @"\infinity"
        | Null -> "<nul>"
        | Undefined -> "<undefined>"

    /// We need a hash function that is commutative under addition and multiplication, so for example,
    /// `hashSP(3x+y) = hashSP(y+3x)`. This makes all comparison operations much easier, as we are delegating
    /// trivial (but cumbersome to implement as is) commutativity checks to a hash function, making the code easier.
    let rec private hashSP (sp: SumProd inref) =

        let inline inner (xs: SumProd list) =
            let mutable result = 0
            let mutable currentHash = 0
            let mutable bitOffset = 0

            let counts = Dictionary<SumProd, int>()

            for x in xs do
                currentHash <- hash x

                match counts.TryGetValue(x, &bitOffset) with
                | true -> counts.[x] <- bitOffset + 1
                | false -> counts.Add(x, bitOffset)

                let lhs = currentHash <<< bitOffset
                let rhs = currentHash >>> (32 - bitOffset)

                result <- result + 37 * (lhs ||| rhs)

            result

        match sp with
        | Variable a -> HashCode.Combine(1, hash a)
        | Integer n -> HashCode.Combine(2, hash n)
        | Float n -> HashCode.Combine(3, hash n)
        | Sum xs -> HashCode.Combine(4, inner xs)
        | Prod xs -> HashCode.Combine(5, inner xs)
        | Pow (a, b) -> HashCode.Combine(6, hashSP &a, hashSP &b)
        | Function (name, args) -> HashCode.Combine(7, name, hash (List.map (fun x -> hashSP &x) args))
        | Infinity -> HashCode.Combine(8)
        | Null -> HashCode.Combine(9)
        | Undefined -> HashCode.Combine(10)

    /// Implements the equality of SumProd expressions.
    let rec private equals (sp1: SumProd) (sp2: obj) =
        match sp2 with
        | :? SumProd as sp2 ->
            match sp1, sp2 with
            | Integer a, Integer b -> a = b
            | Variable a, Variable b -> a = b
            | Function (name1, args1), Function (name2, args2) -> name1 = name2 && args1 = args2
            | Pow (a, expn1), Pow (b, expn2) -> a = b && expn1 = expn2
            | Sum xs, Sum (ys) -> xs = ys
            | Prod xs, Prod (ys) -> xs = ys
            | Null, Null -> true
            | _ -> false
        | _ -> false

    let private addition = function
        | Integer n, b when n = 0I -> b
        | a, Integer n when n = 0I -> a
        | Integer a, Integer b -> Integer (a + b)
        | Float a, Float b -> Float (a + b)
        | Sum [ ], b -> b
        | a, Sum [ ] -> a
        | Sum a, Sum b -> Sum (a @ b)
        | Sum a, b -> Sum (a @ [ b ])
        | a, Sum b -> Sum (a :: b)
        | a, b -> Sum [ a; b ]

    let private multiplication = function
        | Integer n, _ when n = 0I -> Integer 0I
        | _, Integer n when n = 0I -> Integer 0I
        | Integer n, b when n = 1I -> b
        | a, Integer n when n = 1I -> a
        | Integer a, Integer b -> Integer (a * b)
        | Float a, Float b -> Float (a * b)
        | Prod [ ], b -> b
        | a, Prod [ ] -> a
        | Prod a, Prod b -> Prod (a @ b)
        | Prod a, b -> Prod (a @ [ b ])
        | a, Prod b -> Prod (a :: b)
        | Pow (a, b), Pow (a', b') when a = a' -> Pow (a, b + b')
        | a, b -> Prod [ a; b ]

    let private pow = function
        | _, Integer n when n = 0I -> One
        | a, Integer n when n = 1I -> a
        | Integer a, Integer b when b >= bigint Int32.MaxValue -> Pow (Integer a, Integer b)
        | Integer a, Integer b -> Integer (pown a (int b))
        | a, b -> Pow (a, b)

    let public neg = function
        | Integer n when n < 0I -> Integer (abs n)
        | Float n when n < 0.0 -> Float (abs n)
        | Integer n -> Integer -n
        | Float n -> Float -n
        | Negative x -> x
        | x -> Integer -1I * x

    let inline public gcd (a: bigint) (b: bigint) =
        Numerics.BigInteger.GreatestCommonDivisor(a, b)

    let inline public lcm (a: bigint) (b: bigint) =
        a * b / gcd a b

    let inline public GCD (xs: bigint seq) = xs.Aggregate gcd
    let inline public LCM (xs: bigint seq) = xs.Aggregate lcm

    /// GCD for SumProd integers.
    let inline public SPGCD (xs: SumProd seq) =
        Seq.map (function Integer x -> x | x -> raise (NotABigIntException x)) xs
        |> GCD |> Integer

    /// LCM for SumProd integers.
    let inline public SPLCM (xs: SumProd seq) =
        Seq.map (function Integer x -> x | x -> raise (NotABigIntException x)) xs
        |> LCM |> Integer

    /// Generalized GCD, works with integers and fractions.
    let inline public GSPGCD (xs: SumProd seq) =
        assert (xs.All (fun x -> isInteger x || isFrac x))

        let inner a b =
            match a, b with
            | Integer a, Integer b -> Integer (gcd a b)
            | Frac (Integer a, Integer b), Frac (Integer c, Integer d) -> frac (Integer (gcd a c), Integer (lcm b d))
            | Integer a, Frac (Integer b, Integer c) -> frac (Integer (gcd a b), Integer c)
            | Frac (Integer a, Integer b), Integer c -> frac (Integer (gcd a c), Integer b)
            | _ -> raise (Exception "Broken F#")

        xs.Aggregate inner

    /// Generalized LCM, works with integers and fractions.
    let inline public GSPLCM (xs: SumProd seq) =
        assert (xs.All (fun x -> isInteger x || isFrac x))

        let inner a b =
            match a, b with
            | Integer a, Integer b -> Integer (lcm a b)
            | Frac (Integer a, Integer b), Frac (Integer c, Integer d) -> frac (Integer (lcm a c), Integer (gcd b d))
            | Integer a, Frac (Integer b, Integer c) -> frac (Integer (lcm a b), Integer c)
            | Frac (Integer a, Integer b), Integer c -> frac (Integer (lcm a c), Integer b)
            | _ -> raise (Exception "Broken F#")

        xs.Aggregate inner

    let private rational a b =
        let fixSign (p: bigint) (q: bigint) = if q.Sign > 0 then (p, q) else (-p, -q)

        let g = gcd a b

        match fixSign (a / g) (b / g) with
        | a, b when b = 1I -> Integer a
        | a, b -> Integer a * Pow (Integer b, Integer -1I)

    let public frac = function
        | Integer n, _ when n = 0I -> Zero
        | _, Integer n when n = 0I -> Infinity
        | a, Integer n when n = 1I -> a
        | Integer n, b when n = 1I -> Pow (b, Integer -1I)
        | a, b when a = b -> One
        | Integer a, Integer b -> rational a b
        | a, b -> a * Pow (b, Integer -1I)

    let public Zero = Integer 0I
    let public One  = Integer 1I

    /// The representation of expressions in the Liyh kernel is intended to be succinct, considering
    /// only a data structure in the form of a sum of products.
    [<CustomEquality; NoComparison; ReadOnly(true)>]
    type public SumProd =
        | Integer of bigint
        | Variable of string
        | Pow of SumProd * SumProd
        | Float of float
        | Sum of SumProd list
        | Prod of SumProd list
        | Function of string * SumProd list
        | Infinity
        | Undefined
        | Null

        override this.GetHashCode () = hashSP &this
        override this.Equals arg = equals this arg

        member public this.ToLatex = latex this

        static member ( + ) (a: SumProd, b: SumProd) = addition (a, b)
        static member ( - ) (a: SumProd, b: SumProd) = a + neg b
        static member ( * ) (a: SumProd, b: SumProd) = multiplication (a, b)
        static member ( / ) (a: SumProd, b: SumProd) = frac (a, b)
        static member ( *** ) (a: SumProd, b: SumProd) = pow (a, b)

        static member Zero = Zero
        static member One = One

    /// Checks whether the given element exists in the given expression.
    let rec public contains (toFind: SumProd) (sp) =
        let containsIn = contains toFind

        match sp with
        | expr when expr = toFind -> true
        | Variable name when isVariable toFind ->

            match toFind with
            | Variable name' -> name = name'
            | _ -> false

        | Pow (basis, expn) -> containsIn basis || containsIn expn
        | Sum xs -> List.exists containsIn xs
        | Prod xs -> List.exists containsIn xs
        | Function (_, xs) -> List.exists containsIn xs
        | _ -> false

    /// Checks whether all the given elements exist in the given expression.
    let public containsMany (toFind: SumProd list) (src: SumProd) =
        List.forall (fun a -> contains a src) toFind

    /// Checks whether the given expression contains at least one of the elements in the list.
    let public containsOne (toFind: SumProd list) (src: SumProd) =

        let rec inner = function
            | [ ] -> false
            | x :: xs -> if contains x src then true else inner xs

        inner toFind

    /// Checks whether the given expression contains at most one of the elements in the list.
    let public containsAtMostOne (toFind: SumProd list) (src: SumProd) =

        let rec inner = function
            | n, [ ] -> n <= 1
            | n, x :: xs -> if contains x src then inner ((n + 1), xs) else inner (n, xs)

        inner (0, toFind)

    /// Replaces `toFind` with `rep` in the given expression.
    let rec public substitutes (toFind: SumProd) (rep: SumProd) (src: SumProd) =
        let substitutesIn = substitutes toFind rep

        match src with
        | expr when expr = toFind -> rep
        | Sum xs -> Sum(List.map substitutesIn xs)
        | Prod xs -> Prod(List.map substitutesIn xs)
        | Pow (basis, expn) -> Pow(substitutesIn basis, substitutesIn expn)
        | Function (name, xs) -> Function(name, List.map substitutesIn xs)
        | other -> other

    /// Gets the sum's list of the given sum.
    let private getSum = function
        | Sum xs -> xs
        | sp -> raise (NotASumException sp)

    /// Gets the numerator and denominator of the given fraction.
    let private getFrac = function
        | Frac x -> x
        | sp -> raise (NotAFractionException sp)

    /// Assuming `xs` is from a sum, return the general numerator of the sum and the common denominator.
    let private sumOfFrac (xs: SumProd list) =
        let fractions, notFractions = List.partition isFrac xs
        let numerators, denominators = List.map getFrac fractions |> List.unzip

        let denominator = List.reduce ( * ) denominators
        let numerator = List.mapi (fun i x -> x * Prod (List.removeAt i denominators)) numerators

        let numerator =
            Sum <| if notFractions.IsEmpty then numerator
                   else denominator * List.reduce ( + ) notFractions :: numerator

        simp numerator, simp denominator

    /// Assuming `xs` is from a product, return the general numerator of the product and the common denominator.
    let private prodOfFrac (xs: SumProd list) =
        let fractions, notFractions = List.partition isFrac xs
        let numerators, denominators = List.map getFrac fractions |> List.unzip

        let denominator = List.reduce ( * ) denominators
        let numerator = List.reduce ( * ) (numerators @ notFractions)

        simp numerator, simp denominator

    /// If the given expression is a fraction, returns the numerator and denominator.
    let public (|Frac|_|) = function
        | Integer _
        | Float _
        | Variable _
        | Function _ -> None

        | Pow (a, Integer n) when n = -1I -> Some (One, a)
        | Pow (a, Negative b) -> Some (One, Pow (a, b))
        | Sum xs  when List.exists isFrac xs -> Some (sumOfFrac xs)
        | Prod xs when List.exists isFrac xs -> Some (prodOfFrac xs)

        | _ -> None

    /// Sometimes a product contains a product, for example `Prod [a; b; Prod[c; d]; e]`.
    /// This function returns a single product: `Prod[a; b; c; d; e]`.
    let rec private flattenProd (sp: SumProd) =

        let rec inner = function
            | Prod ys :: xs -> inner ys @ inner xs
            | x :: xs -> flattenProd x :: inner xs
            | [] -> []

        match sp with
        | Prod (Prod xs :: ys) -> Prod(inner xs @ inner ys)
        | Prod (x :: xs) -> Prod(flattenProd x :: inner xs)
        | Sum (x :: xs) -> Sum(flattenProd x :: inner xs)
        | Pow (a, b) -> Pow(flattenProd a, flattenProd b)
        | other -> other

    /// Same as `flattenProd`, but returns the list.
    let private flattenProdList =
        flattenProd >> function
            | Prod xs -> xs
            | other -> [ other ]

    /// Checks whether the given expression is composed of integers such that the final result
    /// belongs to the field of integers.
    let public isEvaluableIntegerExpr = function
        | Integer _ -> true
        | Sum xs
        | Prod xs -> xs.All isEvaluableIntegerExpr
        | Pow (a, b) -> isEvaluableIntegerExpr a && isEvaluableIntegerExpr b
        | _ -> false

    /// Checks whether the given expression is composed of floats.
    let public isEvaluableFloatExpr = function
        | Float _ -> true
        | Sum xs
        | Prod xs -> xs.All isEvaluableIntegerExpr
        | Pow (a, b) -> isEvaluableIntegerExpr a && isEvaluableIntegerExpr b
        | _ -> false

    /// Checks whether the given expression is constant with respect to all given variables.
    /// The variables can be any expression except literal constants.
    let public isConstWithRespectTo (variables: SumProd list) =
        assert (List.forall (isLitConst >> not) variables)
        
        function
        | LitConst _ -> true
        | sp -> not (containsMany variables sp)

    /// Checks whether the given SP is clearly constant.
    let public isLitConst = function
        | LitConst _ -> true
        | _ -> false

    /// Checks if the given SP is a variable (whether it has a value or not).
    let public isVariable = function
        | Variable _ -> true
        | _ -> false

    /// Checks whether the given SP is a power.
    let public isPow = function
        | Pow _ -> true
        | _ -> false

    /// Checks whether the given SP is a product.
    let public isProd = function
        | Prod _ -> true
        | _ -> false

    /// Checks whether the given SP is a fraction.
    let public isFrac: SumProd -> bool = function
        | Frac _ -> true
        | _ -> false

    /// Checks whether the given SP is zero.
    let public isZero = function
        | Integer x when x = 0I -> true
        | Float x when x = 0.0 -> true
        | _ -> false

    /// Checks whether the given SP is one.
    let public isOne = function
        | Integer x when x = 1I -> true
        | Float x when x = 1.0 -> true
        | _ -> false

    /// Checks whether the given SP is negative.
    let public isNegative = function
        | Integer x when x < 0I -> true
        | Float x when x < 0.0 -> true
        | Prod xs -> xs.Count isNegative % 2 <> 0
        | _ -> false

    /// Checks whether the given SP is a number.
    let public isInteger = function
        | Integer _ -> true
        | _ -> false

    /// Checks whether the given SP is a float.
    let public isFloat = function
        | Float _ -> true
        | _ -> false

    /// Checks whether the given SP is a number.
    let public isNumeric = function
        | Integer _ -> true
        | Float _ -> true
        | _ -> false

    /// Checks wheter the given SP is a sum.
    let public isSum = function
        | Sum _ -> true
        | _ -> false

    /// Converts the given number into a SumProd number (either an integer or a float depending on the value).
    let public asSPNumeric (value: float) =
        if floor value = value
        then Integer (bigint value)
        else Float value

    /// Pattern which returns the absolute value of a negative quantity.
    let public (|Negative|_|) = function
        | sp when isNegative sp -> Some(absSP sp)
        | _ -> None

    /// A pattern checking whether the given SP is clearly an numeric constant.
    let rec public (|LitConst|_|) = function
        | Variable _ -> None
        | Integer _
        | Float _ as sp -> Some sp
        | Pow (LitConst _, LitConst _) as sp -> Some sp
        | Sum xs
        | Prod xs as sp when xs.All isLitConst -> Some sp
        | Function (_, xs) as sp when xs.All isLitConst -> Some sp
        | _ -> None

    let public (|ConstWithRespectTo|_|) (variables: SumProd list) (sp: SumProd) =
        if isConstWithRespectTo variables sp then Some sp else None

    /// Returns the syntaxic absolute value of the given SP.
    let rec public absSP = function
        | Integer n -> Integer (abs n)
        | Float n -> Float (abs n)
        | Prod xs -> Prod (List.map absSP xs)
        | other -> other

    /// Returns the integer resulting from the given constant expression, assuming it contains only Integer.
    let inline public evalLitConst (sp: SumProd) =

        // Handle integers.
        let rec inner = function
            | Integer x -> x
            | Sum xs -> List.fold (fun acc a -> acc + inner a) 0I xs
            | Prod xs -> List.fold (fun acc a -> acc * inner a) 1I xs
            | Pow (base', expn) -> bigint.Pow(inner base', int (inner expn))
            | t -> raise (NotAConstantLiteralException t)

        // Handle floats.
        let rec inner' = function
            | Float x -> x
            | Sum xs -> List.fold (fun acc a -> acc + inner' a) 0.0 xs
            | Prod xs -> List.fold (fun acc a -> acc + inner' a) 1.0 xs
            | Pow (base', expn) -> inner' base' ** inner' expn
            | t -> raise (NotAConstantLiteralException t)

        match sp with
        | Frac f -> frac f
        | sp when isEvaluableIntegerExpr sp -> Integer (inner sp)
        | sp when isEvaluableFloatExpr sp -> Float (inner' sp)
        | _ -> sp

    let public evalLitConstAsBigInt =
        evalLitConst >>
            function
            | Integer n -> n
            | other -> raise (NotABigIntException other)

    let public evalLitConstAsFloat =
        evalLitConst >>
            function
            | Float n -> n
            | Integer n -> float n
            | other -> raise (NotAFloatException other)

    /// Groups and simplifies the same base powers of the given list, the list is expected to be a product.
    let private samePowers (xs: SumProd list) =
        let dict = Dictionary<int, SumProd * SumProd>()

        let inline updateDict base' expn =
            let mutable found = Null, Null
            let h = hashSP &base'

            match dict.TryGetValue(h, &found) with
            | true -> dict.[h] <- (fst found, snd found + simp expn)
            | false -> dict.Add(h, (simp base', simp expn))

        List.iter
            (function
            | Pow (base', expn) -> updateDict base' expn
            | other -> updateDict other One)
            (flattenProdList (Prod xs))

        [ for (base', expn) in dict.Values do
              match expn with
              | Integer n when n = 0I -> yield One
              | Integer n when n = 1I -> yield base'
              | _ -> yield simp (Pow(base', expn)) ]

        |> function
            | x :: [] -> x
            | xs -> Prod xs

    /// Consider the product of constants with any literal variable (i.e. `SumProd.Variable(_)`) terms.
    let public (|CteTimesSP|) (sp: SumProd) =

        let inline simpProd xs =
            let constants, symbols = List.partition isLitConst xs

            let constant = evalLitConst (Prod constants)
            let symbol = samePowers symbols

            CteTimesSP(constant, (if symbol = sp then symbol else simp symbol))

        match sp with
        | LitConst c -> CteTimesSP(evalLitConst c, Null)
        | Prod _ -> simpProd (flattenProdList sp)
        | _ -> CteTimesSP(One, sp)

    /// Considers the product of constant terms with respect to the given variables, by non-constant terms
    /// with respect to the given variables. For example `3x²` for the variable `x` returns `(3, x²)` and for
    /// example `z*Sin[a]*Exp[a+z]` for the variable `z` will returns `(Sin[a], z*Exp[a+z])`.
    let rec public (|CteTimesSPUsingVars|_|) (variables: SumProd list) (sp: SumProd) =
        assert (not (isSum sp))

        if isConstWithRespectTo variables sp then None
        else

            // Raises the given SP to the given integer power.
            let inline asPow (n: int, sp: SumProd) =
                pow (sp, (Integer (bigint n)))

            // If the given list is empty, return the only item, else returns a SP product.
            let prod = function
                | [ x ] -> x
                | xs    -> Prod xs

            // Returns a list of variables and constants relative to the given variables and indicates
            // the number of times each unique term appears.
            let inline group (xs: SumProd list) =
                xs.GroupBy(id).Select(fun g -> g.Count(), g.Key) |> Seq.toList
                |> List.partition (fun (_, sp) -> containsOne variables sp)

            // Simplify the literal constants from the given expression product.
            let inline simpConst (cs: SumProd list) =
                let c, rest = List.partition isLitConst cs
                evalLitConst (prod c) * prod rest

            match sp with
            | ConstWithRespectTo variables _
            | LitConst _ -> None

            | Prod xs ->
                let variables, constants = group xs
                
                match variables with
                | [] -> None
                | _ ->
                    let term = prod (List.map asPow variables)
                    let constant = List.map asPow constants

                    Some (simpConst constant, term)

            | sp -> Some (One, sp)

    /// Represents the use of a single symbol in terms of the number of times it is added with itself.
    [<Struct; ReadOnly(true)>]
    type private TermUsage =
        { value: SumProd                // A unique symbol
          additiveOccurrence: SumProd } // Integer of times a symbol is added to itself.

    /// Dictionary of Unique Representations of each symbols.
    type private UniqueTermsDict = Dictionary< (* hash code *) int, TermUsage>

    /// Reconstruct the expression from the dictionary.
    let private uniqueTermsToSumProd (uniqueTerms: UniqueTermsDict) =
        [ for x in uniqueTerms.Values do
              match x.additiveOccurrence with
              | Null -> yield x.value
              | Integer n when n = 0I -> yield Zero
              | Integer n when n = 1I -> yield x.value
              | addOcc -> yield addOcc * x.value ]

        |> function
            | CteTimesSP (a, b) :: [] when a = One -> b
            | CteTimesSP (a, b) :: [] -> a * b
            | xs when xs.All isZero -> Zero
            | xs -> List.filter (not << isZero) xs |> Sum

    /// Returns a `TermUsage` based on `oldTU` and modified by `newTU`.
    let inline private updateTermUsage (oldTU: TermUsage) (newTU: TermUsage) =
        let inner = function
            | a, Null -> a
            | Null, b -> b
            | a, b -> a + b

        match oldTU.value, newTU.value with
        | Integer a, Integer b ->
            { value = Integer(a + b)
              additiveOccurrence = Null }

        | _ ->
            { value = oldTU.value
              additiveOccurrence = inner (oldTU.additiveOccurrence, newTU.additiveOccurrence) }

    /// Update the dictionary of unique representations. If the given symbol already exists, then change its
    /// usage information, otherwise add it to the dictionary.
    let inline private updateUniqueTerm
        (uniqueTerms: UniqueTermsDict byref)
        (termHashKey: int)
        (newTermUsage: TermUsage)
        =

        let mutable found =
            { value = Null
              additiveOccurrence = Null }

        match uniqueTerms.TryGetValue(termHashKey, &found) with
        | true ->
            let old = uniqueTerms.[termHashKey]
            uniqueTerms.[termHashKey] <- updateTermUsage old newTermUsage

        | false -> uniqueTerms.Add(termHashKey, newTermUsage)

    /// Binds together two unique representation dictionaries.
    let inline private bindUniqueTerms (ut1: UniqueTermsDict) (ut2: UniqueTermsDict) =
        let mutable result = ut1

        for key in ut2.Keys do
            updateUniqueTerm &result key ut2.[key]

        result

//    /// Builds a dictionary of unique representations from the given `SumProd`.
//    let private buildUniqueTermsDict' = function
//        | Sum xs ->
//            let mutable result = UniqueTermsDict()
//            List.iter (fun x -> result <- bindUniqueTerms result (buildUniqueTermsDict x)) xs
//            result
//
//        | LitConst _ as sp ->
//            let termUsage =
//                { value = evalLitConst sp
//                  additiveOccurrence = Null }
//
//            UniqueTermsDict(dict [ hash 0, termUsage ])
//
//        | CteTimesSP (cte, symb) ->
//            let termUsage =
//                { value = symb
//                  additiveOccurrence = cte }
//
//            UniqueTermsDict(dict [ hashSP &symb, termUsage ])
//
//    /// Builds a dictionary of unique representations from the given `SumProd`.
//    let private buildUniqueTermsDict = Utils.memoize buildUniqueTermsDict'
//
//    /// Simplify the given expression.
//    let private simp' = function
//        | LitConst cte -> evalLitConst cte
//        | other -> (buildUniqueTermsDict >> uniqueTermsToSumProd) other
//
//    /// Performs a basic simplification on the given expression by reducing redundant terms to simpler expressions.
//    let public simp = Utils.memoize simp'

    let public simp _ = SumProd.Null

    /// Isolates the SumProd that meet the predicate.
    let public isolate (pred: SumProd -> bool) = function
        | sp when pred sp -> Some sp, None
        | Sum xs when xs.All pred -> Some (Sum xs), None
        | Prod xs when xs.All pred -> Some (Prod xs), None
        | Sum xs -> let a, b = List.partition pred xs in Some (Sum a), Some (Sum b)
        | Prod xs -> let a, b = List.partition pred xs in Some (Prod a), Some (Prod b)
        | _ -> None, None
