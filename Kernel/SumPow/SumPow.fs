namespace Liyh.Kernel.SumPow

#nowarn "40"    // This warning is activated for the memoized function `simplify` for the active pattern "One".
#nowarn "3391"  // The implicit conversion of an integer into a bigint causes a warning.
#nowarn "25"    // Incomplete pattern-matchings raise warnings (rightly so, but sometimes this is not encountered at runtime).

[<AutoOpen>]
module rec SumPow =
    open System
    open System.Runtime.CompilerServices
    open Liyh.Utils
    open Liyh.Kernel
    open Liyh.Kernel.Constant

    exception public UnknownSumPowExpressionException of SumPow

    /// This module consists of fundamental building `Sum`'s blocks that take into account the flattening of expressions.
    /// These functions should be called every time a sum / term or power is constructed.
    [<AutoOpen>]
    module public PowId =

        /// Creates a power to the exponent 1 from the given expression. If the expression is not itself a power,
        /// then returns it to the power 1, otherwise just return the power.
        let rec public powId =
            function
            | Power(b, One) -> powId b
            //| Power(b, p) -> Pow(b, p)
            | Power(b, p) -> ElementaryOperations.power'(b, p)
            | a -> Pow(a, Const One)

        /// Creates a power to the exponent -1 from the given expression. If the expression is not itself a power,
        /// then returns it to the power -1, otherwise just return the power.
        and public negPowId =
            function
            | Power(b, p) -> Pow(b, -p)
            | a -> Pow(a, Const -One)

        /// Create a one-element term (i.e. a product of one element).
        and public termId =
            function
            | Sum [ a ] -> a
            | Power(a, One) -> termId a
            | a -> Term [ powId a ]

        /// Creates a list of terms (a sum) from the given SumPow list.
        and public manyTermId =

            let rec inner result =
                function
                | [] -> result
                | Sum xs :: rest -> inner (result @ xs) rest
                | other :: rest -> inner (termId other :: result) rest

            inner []

        /// Create a one-element sum (i.e. a sum of one term).
        and public sumId =
            function
            | Term [ Pow(Sum [ term ], One) ] -> sumId term
            | Term [ Pow((PureConstantExpression.PureConstantExpressionInteger _ as b) 
                        ,(PureConstantExpression.PureConstantExpressionInteger _ as p)) ] -> b ** p
            | term -> Sum [ term ]

    /// Various active patterns useful for working around SumPow.
    [<AutoOpen>]
    module public Pattern =
        open ElementaryOperations

        /// An active pattern that represents either a variable (`Name _`), a pure constant (`PureConstantExpression.PureConstantExpression _`) or a
        /// function (`Fun _`). In other words, it's not a sum, a product or a power.
        let public (|SimpleSP|_|) =
            function
            | Name _ as a -> Some a
            | PureConstantExpression.PureConstantExpressionInteger _ as a -> Some a
            | Fun _ as a -> Some a
            | _ -> None

        /// An active pattern that matches the divide-by-zero symbol.
        let public (|DivByZero|_|) =
            function
            | Fun("DivByZero", _) as sp -> Some sp
            | _ -> None

        /// An active pattern that matches the pure constant expression which reduces to the integer 0.
        let public (|Zero|_|) =
            function
            | PureConstantExpression.PureConstantExpressionInteger 0 -> Some()
            | _ -> None

        /// An active pattern that matches the pure constant expression which reduces to the integer 1.
        let public (|One|_|) =
            function
            | PureConstantExpression.PureConstantExpressionInteger 1 -> Some()
            | _ -> None

        /// An active pattern that matches the pure constant expression which reduces to the integer -1.
        let public (|NegOne|_|) =
            function
            | PureConstantExpression.PureConstantExpressionInteger -1 -> Some()
            | _ -> None

        /// An active pattern that matches a term with negative powers ("fractions").
        let public (|TermFrac|_|) =
            function
            | Term term ->

                let negativePower =
                    function
                    | Pow(_, Const n) -> n < Zero
                    | _ -> false

                // We separate positive and negative powers.
                let denominator, numerator = List.partition negativePower term

                // To return a practical denominator, we invert it so that we no longer have a negative power.
                let denominator = List.map (function Pow(a, b) -> Pow(a, -b)) denominator

                // If the denominator is an empty list, then there is no negative power, and therefore no fraction.
                if List.isEmpty denominator then None
                else Some(numerator, denominator)

        /// An active pattern that matches a product with negative powers ("fractions").
        let public (|Frac|_|) =
            function
            | Sum [ TermFrac([], []) ] -> None

            | Sum [ TermFrac([ Pow(b, One) ], []) ] -> Some(b, Const One)
            | Sum [ TermFrac(n, []) ] -> Some(Sum [ Term n ], Const One)

            | Sum [ TermFrac([], [ Pow(b, One) ]) ] -> Some(Const One, b)
            | Sum [ TermFrac([], d) ] -> Some(Const One, Sum [ Term d ])

            | Sum [ TermFrac([ Pow(b, One) ], [ Pow(b', One) ]) ] -> Some(b, b')
            | Sum [ TermFrac(n, d) ] -> Some(Sum [ Term n ], Sum [ Term d ])

            | _ -> None

        /// An active pattern that matches a product and returns the list of powers (a list of tuples).
        let public (|TermProd|_|) (Term term) =
            match term with
            | []
            | [ _ ] -> None
            | lst -> Some(List.map (function Pow(a, b) -> (a, b)) lst)

        /// An active pattern that matches a product and returns the list of powers (a list of tuples).
        let public (|Prod|_|) =
            function
            | Sum [ TermProd tp ] -> Some tp
            | _ -> None

        /// An active pattern that matches a power and returns the tuple `(base, exponent)`.
        let public (|Power|_|) =
            function
            //| Sum [ Term [ Pow(b, p) ] ] when not (Misc.isOne p) -> Some(b, p)
            | Sum [ Term [ Pow(b, p) ] ] -> Some(b, p)
            | _ -> None

        /// An active pattern that matches a product that contains the given expression at least once. In case of Some,
        /// returns a tuple `Prod (prod, n)` where `prod` is the product expression list without the the expression to
        /// be found and where `n` is the number of time it appears.
        let public (|ProdWith|_|) (pred: SumPow -> bool) =
            function
            | Prod [ p ] when pred (power p) -> Some ([ p ], 1)
            | Prod xs ->
                match List.partition (fun p -> pred (power p)) xs with
                | [], _ -> None
                | ts, xs' -> Some(xs', List.length ts)
            | _ -> None

        /// An active pattern that matches a product that contains exactly one the given expression. In case of Some,
        /// returns product expression list without the the expression to be found.
        let public (|ProdWith1|_|) (pred: SumPow -> bool) =
            function
            | ProdWith pred (prod, 1) -> Some prod
            | _ -> None

    /// The module containing SumPow's elementary arithmetic operations.
    module public ElementaryOperations =
        open PureConstantExpression

        /// A pseudo-function symbol (in the sense of elementary functions) that represents division by zero.
        let inline public divByZero (numerator: SumPow) =
            Fun ("DivByZero", [ numerator ])

        let public addition =
            function
            | Const x, Const y -> Const(x + y)

            | Const n, b when isZero n -> b
            | a, Const n when isZero n -> a

            | Frac(n, d), Frac(n', d') -> (n * d' + n' * d) / (d * d')

            | Sum xs, Sum ys -> Sum(xs @ ys)
            | Sum xs, b -> Sum(termId b :: xs)
            | a, Sum ys -> Sum(termId a :: ys)

            | ModularArithmetic.ModularNumber a, ModularArithmetic.ModularNumber b -> ModularArithmetic.modularNumber (a + b)

            | a, b -> Sum [ termId a; termId b ]

        let public subtraction =
            function
            | Const x, Const y -> Const(x - y)
            | Const n, b when isZero n -> -b
            | a, Const n when isZero n -> a
            | ModularArithmetic.ModularNumber a, ModularArithmetic.ModularNumber b -> ModularArithmetic.modularNumber (a - b)
            | a, b -> a + -b

        let public multiplication =
            function
            | Const n, _ when isZero n -> Const Zero
            | _, Const n when isZero n -> Const Zero

            | Const n, b when isOne n -> b
            | a, Const n when isOne n -> a

            | Const x, Const y -> Const(x * y)

            | Sum [ Term x ], Sum [ Term y ] -> Sum [ Term(x @ y) ]
            | Sum [ Term x ], b -> Sum [ Term(powId b :: x) ]
            | a, Sum [ Term y ] -> Sum [ Term(powId a :: y) ]

            | ModularArithmetic.ModularNumber a, ModularArithmetic.ModularNumber b -> ModularArithmetic.modularNumber (a * b)

            | a, b -> Sum [ Term [ powId a; powId b ] ]

        let public negation =
            function
            | Const n -> Const -n
            | Sum sum -> Sum (SimplifiedSum.mapTerm' (fun term -> powId (Const -One) :: term) sum)
            | ModularArithmetic.ModularNumber n -> ModularArithmetic.modularNumber -n
            | sp -> Const -One * sp

        /// Reverse the given term.
        let public inverse =
            List.map (function Pow(a, b) -> Pow(a, -b))

        let public frac =
            function
            | Zero, _ -> Const Zero
            | num, Zero -> divByZero num

            | a, b when a = b -> Const One
            | a, One -> a

            // Instead of dividing two integer and obtaining a double, we simplify the fraction into an irreducible one.
            | Const(CInteger a), Const(CInteger b) ->
                let fixSign p q = if sign q > 0 then (p, q) else (-p, -q)
                let g = intGCD a b

                // Note: Since Constant is currently implemented via `double`, the value/precision of a `bigint`
                // can potentially be lost when converting to `double`.

                match fixSign (a / g) (b / g) with
                | a, b when b = 1 -> Const(fromBigInt a)
                | 1, b -> Sum [ Term [ negPowId (Const(fromBigInt b)) ] ]
                | a, b -> Sum [ Term [ powId (Const(fromBigInt a))
                                       negPowId (Const(fromBigInt b)) ] ]

            | Sum [ Term x ], Sum [ Term y ] -> sumId (Term (x @ inverse y))
            | a, Sum [ Term y ] -> sumId (Term (powId a :: inverse y))
            | Sum [ Term x ], b -> sumId (Term (negPowId b :: x))

            | ModularArithmetic.ModularNumber a, ModularArithmetic.ModularNumber b -> ModularArithmetic.modularNumber (a / b)

            | a, b -> sumId (Term [ powId a; negPowId b])

        let rec public power =
            function
            | Zero, PureConstantExpressionInteger n when n < 0 -> divByZero (Const One)
            | Zero, _ -> Const Zero
            | _, Zero -> Const One
            | Const a, Const b when b > 0 -> Const(a ** b)

            | b, One -> b

            | ModularArithmetic.ModularNumber a, ModularArithmetic.ModularNumber b -> ModularArithmetic.modularNumber (a ** b)

            | b, p -> Sum [ Term [ power'(b, p) ] ]

        /// Transforms the tuple (base, exponent) into a SumPow power.
        let rec public power' =
            function
            | Zero, PureConstantExpressionInteger n when n < 0 -> powId (divByZero (Const One))
            | Power(a, b), One -> power'(a, b)
            | Power(a, One), b -> power'(a, b)
            | Const a, Const b when b > 0 -> Pow(Const(a ** b), Const One)
            | a, b -> Pow(a, b)

        let public modulo =
            function
            | PureConstantExpressionInteger a, PureConstantExpressionInteger b when b <> 0 -> Const (double (a % b))
            | a, b -> Fun("Modulo", [ a; b ])

    /// The module that implements SumPow custom hashing.
    module private Hashing =

        //
        // Since SumPow implements a commutative field, the sum and product hashing are also commutative, meaning that for
        // example the hash of `(a + b + c)` will be the same as that of `(c + a + b)` etc... Ditto for the product. This
        // trick greatly simplifies matters for comparison or encoding in data structures using the hashcode as a key.
        //

        let public hashPow =
            function
            | Pow(a, One) -> hashSumPow a
            | Pow(a, b) -> HashCode.Combine(hashSumPow a, hashSumPow b)

        let public hashTerm (Term xs) =
            commutativeHash xs hashPow

        let public hashSum =
            flip commutativeHash hashTerm

        let public hashProd =
            flip commutativeHash hashPow

        let public hashFunction name args =
            HashCode.Combine(name, (List.map hashSumPow >> hash) args)

        let public hashSumPow =
            function
            | Name name -> HashCode.Combine(Name, name)
            | Const x -> HashCode.Combine(Const, x)
            | Sum xs -> hashSum xs
            | Fun(a, xs) -> HashCode.Combine(Fun, hashFunction a xs)

    /// The module that implements SumPow custom comparaison.
    module private Comparison =

        let public compareSumPow =
            function
            | Const a, Const b -> compare a b
            | PureConstantExpression.PureConstantExpressionInteger a, PureConstantExpression.PureConstantExpressionInteger b -> compare a b
            | Name a, Name b -> compare a b
            | Sum [ x ], Sum [ y ] -> compare x y
            | Sum xs, Sum ys -> compare xs ys
            | Fun(fname1, xs), Fun(fname2, ys) when fname1 = fname2 -> compare xs ys
        //  | _ -> -1
            | a, b -> compare (hash a) (hash b)

        let public compareTerm (Term xs, Term ys) = compare xs ys
        let public comparePow (Pow(a, b), Pow(c, d)) = compare (a, b) (c, d)

    /// The module that implements SumPow custom equality.
    module private Equality =

        let public equalsPow (pow1: Pow) (pow2: obj) =
            match pow2 with
            | :? Pow as pow2 ->
                match pow1, pow2 with
                | Pow(a, b), Pow(c, d) -> a = c && b = d
            | _ -> false

        let public equalsTerm (term1: Term) (term2: obj) =
            match term2 with
            | :? Term as term2 ->
                match term1, term2 with
                | Term xs, Term ys -> Hashing.hashProd xs = Hashing.hashProd ys
            | _ -> false

        /// Basic equality (syntax-based!)
        let public equalsSumPow (sp1: SumPow) (sp2: obj) =
            match sp2 with
            | :? SumPow as sp2 ->
                match sp1, sp2 with
                | Name name1, Name name2 -> name1 = name2
                | Const a, Const b -> a = b
                | Sum xs, Sum ys -> Hashing.hashSum xs = Hashing.hashSum ys
                | Fun(a, xs), Fun(b, ys) -> a = b && xs = ys
                | Sum [ Term [ Pow(a, One) ] ], b -> a = b
                | a, Sum [ Term [ Pow(b, One) ] ] -> b = a
                | _ -> false
            | _ -> false

    /// The module that transforms a SumPow expression into a LaTeX string.
    module private Latex =
        open PureConstantExpression

        let private reorderTerm (term: Pow list) =
            let term =
                List.sortWith
                    (fun (Pow(b, _)) (Pow(b', _)) ->
                        if Misc.isPureConst b && Misc.isPureConst b' then 0
                        elif Misc.isPureConst b then -1
                        elif Misc.isPureConst b' then 1
                        else 0)
                    term

            match List.tryFindIndex (function | Pow(Const cst, One) -> isNegative cst | _ -> false) term with
            | Some i -> "-", List.permute (fun j -> if i = j then 0 elif j = 0 then i else j) term
            | None -> "+", term

        let rec public toLatex =
            function
            | Name name -> name
            | Const cst -> string cst
            | Fun("Complex", [ Re; Im ]) -> sprintf @"\left(%s + i%s\right)" (toLatex Re) (toLatex Im)
            | Power(b, One) -> toLatex b
            | ElemFun.Root(x, nth) -> toLatexRoot x (Const One) nth
            | Frac(num, den) -> sprintf @"\frac{%s}{%s}" (toLatex num) (toLatex den)
            | Power(b, p) -> sprintf @"{%s}^{%s}" (toLatex b) (toLatex p)
            | Fun(fname, arguments) -> toLatexFun fname arguments
            | Sum ss -> toLatexSum ss
            | _ -> failwith "??"

        and private toLatexRoot x n d =
            match (n, d) with
            | PureConstantExpressionInteger 1, PureConstantExpressionInteger nth ->
                if nth = 2 then sprintf @"\sqrt{%s}" (toLatex x)
                else sprintf @"\sqrt[%d]{%s}" nth (toLatex x)
            | n, PureConstantExpressionInteger nth -> sprintf @"\sqrt[%d]{%s}" nth (toLatex (x ** n))
            | PureConstantExpressionInteger 1, nth -> sprintf @"\sqrt[%s]{%s}" (toLatex nth) (toLatex x)
            | n, d -> sprintf @"\sqrt[%s]{%s}" (toLatex d) (toLatex (x ** n))

        and private toLatexPow =
            function
            | Pow(b, PureConstantExpressionInteger p) when p < 0 -> sprintf @"\frac{%d}{%s}" -p (toLatexValue b)
            | Pow(b, Frac(num, den)) -> toLatexRoot b num den
            | Pow(Sum _ as b, One) -> sprintf @"\left(%s\right)" (toLatex b)
            | Pow(Sum _ as b, p) -> sprintf @"\left(%s\right)^{%s}" (toLatex b) (toLatex p)
            | Pow(One, One) -> ""
            | Pow(b, One) -> toLatex b
            | Pow(b, p) -> sprintf @"{%s}^{%s}" (toLatex b) (toLatex p)

        and private toLatexTerm (Term term) =
            let ssign, term = reorderTerm term

            /// Manages `+` or `-` signs as well as `\cdot` when needed.
            let inline peekFoldInner acc term next =
                let sa = toLatexPow term

                if sa = "" then if acc = "" && Option.isNone next then "1" else acc
                elif sa.StartsWith "-" then sprintf @"%s{%s}" acc sa
                else sprintf @"%s{%s}" acc sa

                +

                match next with
                | Some(Pow(Const _, _) | Pow(Prod _, _) | Pow(Sum _, _)) -> @"\cdot "
                | _ -> " "

            let result = List.peekFold peekFoldInner String.Empty term
            ssign, result

        and private toLatexSum (sum: Term list) =
            let terms =
                List.map
                    (fun (ssign, sterm) ->
                        if ssign = "-" then sterm
                        else sprintf @"+ %s" sterm)
                    (List.map toLatexTerm sum)

            let r = String.concat "" terms
            if r.StartsWith "+" then r.[1..] else r

        and private toLatexFun (fname: string) (arguments: SumPow list) =
            let latexArguments = System.String.Join(',', List.map toLatex arguments)

            let fname =
                match fname with
                | "Sqrt" -> sprintf @"\sqrt{%s}"
                | "Abs" -> sprintf @"\left|{%s}\right|"
                | "Exp" -> sprintf @"e^{%s}"
                | fname -> sprintf @"\text{%s}\left(%s\right)" fname

            fname latexArguments

    /// The module that interfaces with Symbolic.
    [<AutoOpen>]
    module public Symbolic =

        /// Assuming this is feasible, convert the given symbol to SumPow. Throw `UnknownSymbolicMatchException` otherwise.
        let rec public toSumPow =
            function
            | { atom = Atomic.Identifier name
                attributes = [] } -> SumPow.Name name

            | { atom = Atomic.Identifier "+"
                attributes = xs }
            | { atom = Atomic.Identifier "Sum"
                attributes = xs } -> List.reduce ( + ) (List.map toSumPow (getArgsOnly xs))

            | { atom = Atomic.Identifier "-"
                attributes = [ (_, x) ] }
            | { atom = Atomic.Identifier "Neg"
                attributes = [ (_, x) ] } -> ElementaryOperations.negation (toSumPow x)

            | { atom = Atomic.Identifier "-"
                attributes = xs }
            | { atom = Atomic.Identifier "Sub"
                attributes = xs } -> List.reduce ( - ) (List.map toSumPow (getArgsOnly xs))

            | { atom = Atomic.Identifier "*"
                attributes = xs }
            | { atom = Atomic.Identifier "Prod"
                attributes = xs } -> List.reduce ( * ) (List.map toSumPow (getArgsOnly xs))

            | { atom = Atomic.Identifier "**"
                attributes = [ (_, b); (_, p) ] }
            | { atom = Atomic.Identifier "Pow"
                attributes = [ (_, b); (_, p) ] } -> (toSumPow b) ** (toSumPow p)

            | { atom = Atomic.Identifier "/"
                attributes = [ (_, a); (_, b) ] }
            | { atom = Atomic.Identifier "Div"
                attributes = [ (_, a); (_, b) ] } -> (toSumPow a) / (toSumPow b)

            | { atom = Atomic.Identifier name
                attributes = xs } -> SumPow.Fun(name, List.map (fun (_, arg) -> toSumPow arg) xs)

            | { atom = Atomic.Const cst
                attributes = [] } -> SumPow.Const cst

            | other -> raise (UnknownSymbolicMatchException other)

        /// Converts the SumPow expression into a symbol.
        let rec public toSymbolic (sp: SumPow) =

            let inline powToSymb (Pow(a, b)) =
                { atom = Atomic.Identifier "Pow"
                  attributes = [ (null, toSymbolic a); (null, toSymbolic b) ] }

            let inline termToSymb (Term xs) =
                if List.length xs = 1 then
                    powToSymb xs.Head
                else
                    { atom = Atomic.Identifier "Mul"
                      attributes = List.map (fun pow -> null, powToSymb pow) xs }

            match sp with
            | SumPow.Name name ->
                { atom = Atomic.Identifier name
                  attributes = [] }

            | SumPow.Const cst ->
                { atom = Atomic.Const cst
                  attributes = [] }

            | SumPow.Sum sum ->
                { atom = Atomic.Identifier "Sum"
                  attributes = List.map (fun term -> null, termToSymb term) sum }

            | SumPow.Fun(fname, args) ->
                { atom = Atomic.Identifier fname
                  attributes = List.map (fun sp -> null, toSymbolic sp) args }

    /// Represents a symbolic value that is used for mathematical expressions.
    [<CustomEquality; CustomComparison; Symbolic>]
    type public SumPow =
        /// A `Name` represents a variable in a broadest sense (an unknown, a variable, a parameter, a nominated constant, ...)
        | Name of name: string

        /// A `Const` is a pure number.
        | Const of cst: Constant

        /// A `Sum` is a list of products of powers.
        | Sum of sum: Term list

        /// A `Fun` is a function in the broadest sense (a name that associates arguments).
        | Fun of fname: string * args: SumPow list

        override this.GetHashCode() = Hashing.hashSumPow this
        override this.Equals arg = Equality.equalsSumPow this arg
        override this.ToString() = Latex.toLatex this

        // -- Implement interfaces -- //

        interface IComparable with
            member sp1.CompareTo obj =
                match obj with
                | :? SumPow as sp2 -> Comparison.compareSumPow (sp1, sp2)
                | _ -> invalidArg "obj" "cannot compare value of different types"

        interface ISymbolic with
            member this.ToSymbolic() = Symbolic.toSymbolic this
            member this.ToLatex() = Some(Latex.toLatex this)
            member this.ToLatexOrString() = Latex.toLatex this
            member this.Hash = hash this

        // -- Standards -- //

        static member op_Addition(a: SumPow, b: SumPow) = ElementaryOperations.addition (a, b)
        static member op_Subtraction(a: SumPow, b: SumPow) = ElementaryOperations.subtraction (a, b)
        static member op_Multiply(a: SumPow, b: SumPow) = ElementaryOperations.multiplication (a, b)
        static member op_Division(a: SumPow, b: SumPow) = ElementaryOperations.frac (a, b)
        static member Pow(a: SumPow, b: SumPow) = ElementaryOperations.power (a, b)
        static member op_UnaryNegation(a: SumPow) = ElementaryOperations.negation a

        // -- Overloading with integers -- //

        static member op_Addition(a: int, b: SumPow) = Const(Constant a) + b
        static member op_Addition(a: SumPow, b: int) = a + Const(Constant b)
        static member op_Subtraction(a: int, b: SumPow) = Const(Constant a) - b
        static member op_Subtraction(a: SumPow, b: int) = a - Const(Constant b)
        static member op_Multiply(a: int, b: SumPow) = Const(Constant a) * b
        static member op_Multiply(a: SumPow, b: int) = a * Const(Constant b)
        static member op_Division(a: int, b: SumPow) = Const(Constant a) / b
        static member op_Division(a: SumPow, b: int) = a / Const(Constant b)
        static member Pow(a: int, b: SumPow) = Const(Constant a) ** b
        static member Pow(a: SumPow, b: int) = a ** Const(Constant b)

        static member op_Explicit(a: int) = SumPow.Const(Constant a)

    /// A "Term" is a product of powers.
    [<Struct; CustomEquality; CustomComparison>]
    type public Term =
        /// A `Term` is a product of powers.
        | Term of Pow list

        override this.GetHashCode() = Hashing.hashTerm this
        override this.Equals arg = Equality.equalsTerm this arg

        interface IComparable with
            member term1.CompareTo obj =
                match obj with
                | :? Term as term2 -> Comparison.compareTerm (term1, term2)
                | _ -> invalidArg "obj" "cannot compare value of different types"

    /// A "Pow" is a SumPow tuple.
    [<Struct; CustomEquality; CustomComparison>]
    type public Pow =
        /// A `Pow` is a SumPow tuple.
        | Pow of SumPow * SumPow

        override this.GetHashCode() = Hashing.hashPow this
        override this.Equals arg = Equality.equalsPow this arg

        interface IComparable with
            member pow1.CompareTo obj =
                match obj with
                | :? Pow as pow2 -> Comparison.comparePow (pow1, pow2)
                | _ -> invalidArg "obj" "cannot compare value of different types"

    /// This module contains some utilities that make it easier to manipulate SumPow's sums.
    module public SimplifiedSum =

        exception public NotASimplifiedSum of SumPow

        /// In SumPow, a sum is a list of products of powers, represented more elegantly by single constructors `Term` and `Pow`.
        /// These last two types are abstractions which it's sometimes useful to dispense with for simplicity's sake, so a
        /// "simplified sum" represents SumPow's sum as the following type without `Term` nor `Pow` constructors.
        type public SimplifiedSum = (SumPow * SumPow) list list

        /// Convert the given `SumPow` sum (list of terms) to `SimplifiedSum`.
        let inline public simplifiedSum (sum: Term list) : SimplifiedSum =
            [ for Term term in sum -> [ for Pow(b, p) in term -> (b, p) ] ]

        /// Convert the given `SumPow` sum to `SimplifiedSum`.
        let inline public simplifiedSum' (expr: SumPow) : SimplifiedSum =
            match expr with
            | Sum terms -> simplifiedSum terms
            | other -> raise (NotASimplifiedSum other)

        /// Convert the given `SimplifiedSum` to `SumPow`.
        let public simplifiedSumToSum (ss: SimplifiedSum) =
            let inline makeTerm term = [ for (b, p) in term -> ElementaryOperations.power'(b, p) ]
            Sum [ for term in ss -> (Flatten.flattenTerm >> Term) (makeTerm term) ]

        /// Active pattern for `SumPow`'s sum to `SimplifiedSum`.
        let public (|SimplifiedSum|_|) =
            function
            | Sum xs -> Some(simplifiedSum xs)
            | _ -> None

        /// Map each term of the simplified sum with the given function.
        let public mapTerm (mapping: (SumPow * SumPow) list -> 't) (ss: SimplifiedSum) =
            List.map mapping ss

        /// Map each power of the simplified sum with the given function.
        let public mapPow (mapping: (SumPow * SumPow) -> 't) (ss: SimplifiedSum) =
            List.map (List.map mapping) ss

        /// Map each power of the simplified sum with the given function and flatten the result.
        let public mapPowFlatten (mapping) (ss: SimplifiedSum) =
            (List.map (List.map mapping) >> List.flatten) ss

        //
        // It is not necessary to switch to the `SimplifiedSum` representation to work more easily with SumPow:
        //

        /// Map each term of the SumPow sum with the given function.
        let public mapTerm' (mapping: Pow list -> Pow list) (ts: Term list) =
            List.map (function Term term -> Term(mapping term)) ts

        /// Map each power of the SumPow sum with the given function.
        let inline public mapPow' (mapping: SumPow -> SumPow -> Pow) (ts: Term list) =
            List.map (function Term term -> Term(List.map (function Pow(b, p) -> mapping b p) term)) ts

        /// Map each power of the SumPow sum with the given function and keep the current index.
        let inline public mapiPow' (mapping: int -> SumPow -> SumPow -> Pow) (ts: Term list) =
            List.map (function Term term -> Term(List.mapi (fun i (Pow(b, p)) -> mapping i b p) term)) ts

        /// Converts the sum into a SumPow list.
        let public sumAsSumPowList =
            function
            | Sum xs -> List.map sumId xs
            | other -> [ other ]

        /// An active pattern that converts the sum into a SumPow list.
        let inline public (|SumList|_|) (sp: SumPow) =
            let t = sumAsSumPowList sp
            if List.length t <= 1 then None else Some t

    /// A "pure constant expression" is an expression containing no variables or parameters, just numbers. For simplicity,
    /// even constants such as pi and e are not considered (for now). This module provides utilities for simplifying and
    /// working with constant expressions or matching them.
    /// 
    /// The simplifier (hopefully) handles integers, rationals, powers, fractions, roots, sums and products.
    module public PureConstantExpression =
        open SimplifiedSum
        open ElementaryOperations
        open ElemFun

        exception public ExpressionIsNotPureConstantException of SumPow
        exception public ExpressionIsNotPureConstantRationalException of SumPow

        /// This module allow to simplify nested radical expressions.
        module private Denesting =

            /// Check whether `x` is a perfect `nth`-root, if so then returns the result.
            let private tryPerfectRoot (x: bigint) (nth: int) =
                if x < 0 && nth % 2 = 0 then None else

                let rec bsearch low high =
                    if low > high then None
                    else
                        let mid = low + (high - low) / 2I
                        let midPow = pown mid nth
                        if midPow = x then Some low
                        elif midPow < x then bsearch (mid + 1I) high
                        else bsearch low (mid - 1I)

                bsearch 0 x

            /// Simplifies each perfect root of the given expression.
            let rec public simplifyAllPerfectRoots =
                function
                | Const cst -> Const cst
                | Root(Const (CBigInteger x), Const (CInteger nth)) as sp when nth > 1 ->
                    match tryPerfectRoot x nth with
                    | Some r -> Const (fromBigInt r)
                    | None -> sp
                | Fun(fname, args) -> Fun(fname, List.map simplifyAllPerfectRoots args)
                | Sum xs -> Sum (mapPow' (fun b p -> power' (simplifyAllPerfectRoots b, simplifyAllPerfectRoots p)) xs)
                | other -> other

            /// Returns a measure of the degree of nesting of a radical.
            let rec private nestingLevel =
                function
                | Const _ -> 1
                | Root(x, Const nth) when nth > 1 -> nestingLevel x + 1
                | Prod xs -> List.max (List.map nestingLevel (List.map power xs))
                | Sum xs -> List.sum (List.map (sumId >> nestingLevel) xs)
                | _ -> 1

            let private split =
                function
                | Sum [ x ] -> Sum [ x ], Const Zero
                | Sum xs ->
                    let a, b = List.splitAt ((List.length xs - 1) / 2) xs
                    Sum a, Sum b
                | other -> other, Const Zero

            let rec public intSqrtDenesting (sp: SumPow) = failwith "TODO: denesting radicals"

        /// Type of result possible after simplifying an integer root.
        [<Struct; RequireQualifiedAccess; NoEquality; NoComparison>]
        type private SimpIntRoot =
            | Int         of int: int // a simple integer
            | IrredRoot   of irredRoot: (int * int) // an irreductile root x & nth
            | IntRootProd of intRootProd: (int * (int * int)) // the product of an irreductile root and an integer coefficient

        /// Each negative number of the given product is transformed into the product of its absolute value and `-1`.
        let inline private shneg (prod: (SumPow * SumPow) list) =

            let inline inner acc (b, p) =
                match b with
            //  | PureConstantExpressionInteger n when n < 0 // risky?
                | Const(CBigInteger n) when n < 0 -> (Const -1, p) :: (Const(fromBigInt (abs n)), p) :: acc
                | other -> (other, p) :: acc

            List.fold inner [] prod

        let private csimplifyIntRoot (x: int) (nth: int) =
            let inline simplifyNthRoot x n =

                let rec loop i c d =
                    if i * i > d then (c, d)
                    elif d % (pown i n) = 0
                    then loop i (c * i) (d / (pown i n))
                    else loop (i + 1) c d

                loop 2 1 x

            match simplifyNthRoot x nth with
            | c, 1 -> SimpIntRoot.Int c
            | 1, d -> SimpIntRoot.IrredRoot (d, nth)
            | c, d -> SimpIntRoot.IntRootProd (c, (d, nth))

        let private csimplifyIntRootAsSumPow (x: int) (nth: int) =
            match csimplifyIntRoot x nth with
            | SimpIntRoot.Int r -> Const r
            | SimpIntRoot.IrredRoot(x, nth) -> Fun("Root", [ Const x; Const nth ])
            | SimpIntRoot.IntRootProd (c, (x, nth)) -> c * Fun("Root", [ Const x; Const nth ])

        /// Checks if the given expression is a "pure constant" (i.e. an expression containing no `Name string` data).
        /// The returned expression is unvalued.
        [<MethodImpl(MethodImplOptions.AggressiveOptimization)>]
        let rec public (|PureConstantExpression|_|) =
            function
            | Name _ -> None
            | Const _ as c -> Some c
            | SimplifiedSum ss as c ->
                let isPureConstPow (b, p) = isPureConstantExpression b && isPureConstantExpression p
                if List.forall (List.forall isPureConstPow) ss then Some c
                else None

            | DivByZero _ as sp -> Some sp
            | Fun(_, args) as c ->
                if List.forall isPureConstantExpression args then Some c
                else None

            | other -> raise (UnknownSumPowExpressionException other)

        /// An active pattern that matches an integer constant expression and evaluates it.
        and public (|PureConstantExpressionInteger|_|) =
            function
            | Const(CInteger c) -> Some c
            | PureConstantExpression pc ->

                match csimplify pc with
                | Const(CInteger c) -> Some c
                | _ -> None

            | _ -> None

        /// An active pattern that matches a natural constant expression and evaluates it.
        and public (|PureConstantExpressionNatural|_|) =
            function
            | PureConstantExpressionInteger x when x >= 0 -> Some x
            | _ -> None

        /// An active pattern that matches a rational constant expression and simplify it.
        and public (|PureConstantExpressionRational|_|) =
            function
            | Frac(PureConstantExpressionInteger cnum, PureConstantExpressionInteger cden) -> Some (cnum, cden)
            | _ -> None

        /// An active pattern that matches a floating-point expression.
        and public (|PureConstantExpressionFloat|_|) =
            function
            | Const(CFloat c) -> Some c
            | PureConstantExpression pc ->

                match csimplify pc with
                | Const(CFloat c) -> Some c
                | _ -> None

            | _ -> None

        /// Assuming that the given expression is a pure constant (i.e. an expression containing no variables), then return
        /// the constant in a simplified form (that is not approximate to the initial expression). If the initial expression
        /// involves floating-point constants, then the simplification is subject to the inaccuracies.
        and public csimplify =
            id//FixedPoint.tryFixedPoint 5 // Is the fixed point necessary?
            <| function
                | Const _ as cst -> cst
                | Power(b, One) -> csimplify b
                | Power(Root(x, PureConstantExpressionInteger nth), PureConstantExpressionInteger p) when p = nth ->                    
                    csimplify x

                | Power(Prod prod, p) ->
                    let p = csimplify p
                    let pprod = List.map (fun (b, p') -> power' (b, csimplify (p * p'))) prod
                    csimplify (sumId (Term pprod))

                | Power(b, p) -> power (csimplify b, csimplify p)

                | Root(PureConstantExpressionInteger 1, _) -> Const One
                | Root(PureConstantExpressionInteger x, PureConstantExpressionInteger nth) ->
                    csimplifyIntRootAsSumPow x nth

                | Frac(PureConstantExpressionInteger 1, Root(PureConstantExpressionInteger x, PureConstantExpressionNatural nth)) ->
                    let t = (csimplifyIntRootAsSumPow x nth) ** (nth - 1)
                    csimplify (csimplify t / x)

                | Root(PureConstantExpressionRational (a, b), PureConstantExpressionNatural nth) ->
                    let a = csimplifyIntRootAsSumPow a nth
                    let b = csimplifyIntRootAsSumPow b nth
                    csimplify (a / b)

                | Prod prod -> csimplifyProd prod
                | Sum terms -> csimplifySum terms
                | Fun(fname, args) -> Fun(fname, List.map csimplify args)
                | other -> other

        and private csimplifyProd (prod: (SumPow * SumPow) list) =
            let prod = shneg prod

            let rec makeSimp omap rmap =
                function
                | [] -> omap, rmap

                | (Root(PureConstantExpressionInteger x, PureConstantExpressionInteger nth), One) :: rest ->
                    makeSimpIntRoot x nth omap rmap rest

            // TODO (inverse roots)
            //  | (Root(PureConstantExpressionInteger x, PureConstantExpressionInteger nth), NegOne) :: rest ->
            //      makeSimpIntRoot x nth omap rmap rest

                | (b, p) :: rest ->
                    let omap = Map.addOrUpdate (csimplify b) p omap (( + ) p)
                    makeSimp omap rmap rest

            and makeSimpIntRoot x nth omap rmap rest =
                let inline updateOMap k v = Map.addOrUpdate k v omap (( + ) 1 >> csimplify)
                let inline updateRMap k v = Map.addOrUpdate k v rmap (( * ) v >> csimplify)

                match csimplifyIntRoot x nth with
                | SimpIntRoot.Int c ->
                    let omap = updateOMap (Const c) (Const One)
                    makeSimp omap rmap rest

                | SimpIntRoot.IrredRoot(x, nth) ->
                    let rmap = updateRMap (Const nth) (Const x)
                    makeSimp omap rmap rest

                | SimpIntRoot.IntRootProd(c, (x, nth)) ->
                    let omap = updateOMap (Const c) (Const One)
                    let rmap = updateRMap (Const nth) (Const x)
                    makeSimp omap rmap rest

            let inline folder (iacc, facc, oacc) b p =
                match b, p with
                | PureConstantExpressionInteger b, PureConstantExpressionInteger p when p > 0 ->
                    (Const (pown b p) * iacc, facc, oacc)

                | PureConstantExpressionInteger b, PureConstantExpressionInteger p when p < 0 ->
                    (iacc, Const (pown b (abs p)) * facc, oacc)

                | b, p ->
                    (iacc, facc, oacc * power (b, p))

            // The calculations are divided into four parts:
            //  a. manage the product of roots
            //  b. manage the product of integers
            //  c. manage the product of inverted integers
            //  d. manage the product of other factors

            let omap, rmap = makeSimp Map.empty Map.empty prod
            let a = Map.fold (fun acc nth x -> acc * Fun("Root", [ x; nth ])) (Const One) rmap
            let b, c, d = Map.fold folder (Const One, Const One, Const One) omap

            // Version that only manages roots and "other" factors without distinction:
            //   let omap, rmap = makeSimp Map.empty Map.empty prod
            //   let a = Map.fold (fun acc b p -> acc * power (b, p)) (Const One) omap
            //   let b = Map.fold (fun acc nth x -> acc * Fun("Root", [ x; nth ])) (Const One) rmap
            // 
            //   a * b

            (b/c) * a * d

        and private csimplifyTerm =
            function
            | TermProd tp -> csimplifyProd tp
            | other -> sumId other

        and private csimplifySum =
            function
            | [] -> invalidArg "terms" "empty sum list"
            | [ term ] -> csimplifyTerm term
            | terms ->
                let terms = List.map csimplifyTerm terms
                let rationals, others =
                    List.partition (fun x -> isPureConstantExpressionRational x
                                          || isPureConstantExpressionInteger x) terms

                let others = List.map csimplify others

                if List.isEmpty rationals then Sum (manyTermId others)
                else
                    let irat =
                        function
                        | PureConstantExpressionRational (cnum, cden) -> (cnum, cden)
                        | PureConstantExpressionInteger n -> (n, 1)
                        | other -> raise (ExpressionIsNotPureConstantRationalException other)

                    let irats = List.map irat rationals
                    let lcm = List.aggregate intLCM (List.map snd irats)
                    let num = List.fold (fun acc (num, den) -> acc + (num * lcm / den)) 0 irats
                    let irat = Const num / Const lcm

                    Sum (manyTermId (irat :: others))

        /// Checks whether the given expression contains no `Name _`.
        let public isPureConstantExpression =
            function
            | PureConstantExpression _ -> true
            | _ -> false

        /// Checks whether the given expression reduces to an integer.
        let public isPureConstantExpressionInteger =
            function
            | PureConstantExpressionInteger _ -> true
            | _ -> false
        
        /// Checks whether the given expression reduces to an integer.
        let public isPureConstantExpressionNatural =
            function
            | PureConstantExpressionNatural _ -> true
            | _ -> false

        /// Check whether the given expression reduces to a rational.
        let public isPureConstantExpressionRational =
            function
            | PureConstantExpressionRational _ -> true
            | _ -> false

        /// Checks whether the given expression reduces to a floating-point number.
        let public isPureConstantExpressionFloat =
            function
            | PureConstantExpressionFloat _ -> true
            | _ -> false

    /// A SumPow expression is said to be "flattened" if it contains no nodes of the form `Term [ Pow(Sum [ Term term ], One) ]`.
    /// In other words, flattening consists of modifying the SumPow representation to meet this criterion. This is very
    /// important for the proper functioning and optimality of the algorithms used almost everywhere with SumPow, particularly
    /// with regard to simplifications and expansions.
    module public Flatten =
        open ElementaryOperations
        open SimplifiedSum

        let private isFlatTerm =
            function
            | Term [ Pow(Sum [Term _], One) ] -> false
            | _ -> true

        let private isSumOfPowersWithSumBase =
            let inn1 (Pow(b, p)) = Misc.isSum b && Misc.isOne p
            let inn2 (Term term) = List.forall inn1 term

            List.forall inn2

        /// Determines whether the given SumPow expression is flattened.
        let rec public isFlat =
            function
            | Sum sum -> List.forall isFlatTerm sum && not (isSumOfPowersWithSumBase sum)
            | _ -> true

        /// Rewrite all `Term [ Pow(Sum [ Term term ], One) ]` to `Term term` recursively in the given SumPow.
        let rec public flatten (sp: SumPow) =
            if isFlat sp then sp else
            match sp with
            | Power(b, One) -> flatten b
            | Power(b, p) -> power(flatten b, flatten p)
            | Sum sum when isSumOfPowersWithSumBase sum ->
                let inn1 (Pow(Sum xs, One)) = xs
                let inn2 (Term term) = List.collect inn1 term

                Sum (List.collect inn2 sum)
            | Sum sum -> Sum ((mapTerm' flattenTerm) sum)
            | other -> other

        /// Rewrite all `Term [ Pow(Sum [ Term term ], One) ]` to `Term term` recursively in the given term.
        and public flattenTerm =

            let rec inner result =
                function
                | [] -> result

                | Pow (Sum [ Term term ], One) :: tail ->
                    inner (inner [] term @ result) tail

                | Pow (Sum sum, p) :: tail ->
                    let sum = mapTerm' (inner []) sum
                    inner (power' (Sum sum, p) :: result) tail

                | other :: tail -> inner (other :: result) tail

            inner []

    /// Elementary simplifications, concerned with common terms that simplify each other.
    /// This simplification module is the basis for all other simplifications in Liyh.
    module public Simplification =
        open ElementaryOperations
        open SimplifiedSum
        open Flatten

        //
        // P͟e͟r͟f͟o͟r͟m͟a͟n͟c͟e͟ ͟n͟o͟t͟e͟: the current implementation uses the `Map` type from the F# library at the heart of its
        // calculations. We use it because it's what the standard lib provides, has good overall performance and is
        // nice to use in a functional style. However, our use of it in the algorithms below is not the most suitable
        // for an AVL tree, as there are mostly insertions, which has a cost on tree balancing (a cost that also depends
        // on the SumPow comparison, which is not free!) For better performance, the use of a `Dictionary` would be more
        // appropriate, but I haven't yet taken the time to do so... Also it's uglier.
        //
        // What's more, most of SumPow's rewriting methods assume a flattened expression, i.e. basically no expression that
        // contains any `Term [ Pow(Sum [Term term], One) ]`. Most methods directly rewrite a flattened expression, but
        // sometimes this isn't handled for some reason, hence the definition of a flattening function, `flatten`. This
        // function is relatively costly in terms of time complexity. I'd really like to do without it, as it has a
        // significant impact on performance, and I also suspect that it's just correcting badly written code that doesn't
        // directly return a flattened expression...
        // That said, it's still useful when it's not possible to return a flattened expression in a simple way.
        //

        /// Cleans a product by removing terms equal to one.
        let public basicTermSimp =
            List.filter (function Pow(b, p) -> p <> Const Zero && (b, p) <> (Const One, Const One))

        /// Assuming that the given expression is a pure constant (i.e. an expression containing no variables), then return
        /// the constant in a simplified form (that is not approximate to the initial expression). If the initial expression
        /// involves floating-point constants, then the simplification is subject to the inaccuracies.
        let public simpPureConst (sp: SumPow) =
            if not (PureConstantExpression.isPureConstantExpression sp) then
                raise (PureConstantExpression.ExpressionIsNotPureConstantException sp)

            PureConstantExpression.csimplify sp

        /// Basic simplifies the fraction, given in numerator and denominator form. Returns a SumPow.
        let private simpFrac (num: SumPow) (den: SumPow) =
            match simplify num, simplify den with
            // The easiest cases we can handle: divise a product by another product.

            | Sum [ Term x ], Sum [ Term y ] ->
                let factor, term = (flattenTerm >> simpProd) (x @ inverse y)
                factor * Sum [ Term term ]

            | a, Sum [ Term y ] ->
                let factor, term = simpProd (powId a :: inverse y)
                factor * Sum [ Term term ]

            | Sum [ Term x ], b ->
                let factor, term = simpProd (negPowId b :: x)
                factor * Sum [ Term term ]

            // Otherwise
            | num, den -> ElementaryOperations.frac(num, den)

        /// Simplify the terms in common in the given product (a list of powers).
        [<MethodImpl(MethodImplOptions.AggressiveOptimization)>]
        let public simpProd (list: Pow list) =

            // The algorithm works as follows: we build a dictionary (`Map`) with each power (base, exponent) of the list. The
            // dictionary keys are the bases of the powers and the values are the exponents. When a new element is added but a
            // key already exists, this means we have a product of two common terms, so we modify the value associated with
            // the key by adding the two exponents. The classic rules of power algebra then follow.

            // The algorithm also keeps the constant factor of the product separate. If a constant power is encountered, then
            // this constant factor is multiplied.

            let rec makeSimp result constant =
                function
                | [] -> (constant, result)

                | Pow(One, One) :: xs
                | Pow(_, Zero) :: xs -> makeSimp result constant xs

                | Pow(Const a, Const b) :: xs ->
                    match b with
                    | b when isOne b -> makeSimp result (constant * Const a) xs
                    | b when isNegative b -> makeSimp result (constant / Const a) xs
                    | b -> makeSimp result (constant * Const(a ** b)) xs

                | Pow(Power(b, p), p') :: xs -> // (A^X)^Y = A^(X*Y)
                    makeSimp result constant (power' (b, p * p') :: xs)

                | Pow(b, p) :: xs ->
                    match Map.tryFind b result with
                    | None -> makeSimp (Map.add b p result) constant xs
                    | Some v ->
                        match v + p with
                        | Zero -> makeSimp (Map.remove b result) constant xs
                        | newPow -> makeSimp (Map.update result b newPow) constant xs

            // Once the dictionary (Map) has been created, all we need to do is convert it into a list of powers, thus
            // satisfying our definition of a SumPow product.

            let constant, dict = makeSimp Map.empty (Const One) list
            let sdict = List.map (fun (a, b) -> power' (simplify a, simplify b)) (Map.toList dict)

            (simpPureConst constant, flattenTerm sdict)

        /// Simplify the terms in common in the given sum (a list of terms).
        [<MethodImpl(MethodImplOptions.AggressiveOptimization)>]
        let private simpSum (sum: Term list) =

            // The algorithm works as follows: we build a dictionary (`Map`) with each term (a product) of the list. The
            // dictionary keys are the variables (in the broadest sense) and the values are the factors. When a new element is
            // added but a key already exists, this means we have a sum of two common terms, so we modify the value associated
            // with the key by adding the two factors. The classic rules of algebra then follow.

            // The algorithm also keeps the constant term of the sum separate. If a constant term is encountered, then
            // this constant factor is added.

            let rec makeSimp result constant =
                function
                | [] -> (constant, result)

                | Term term :: xs ->
                    match (simpProd term) with
                    | PureConstantExpression.PureConstantExpression c, [] -> makeSimp result (constant + c) xs

                    | factor, term ->
                        match Map.tryFind term result with
                        | None -> makeSimp (Map.add term factor result) constant xs
                        | Some v ->
                            match factor + v with
                            | Zero -> makeSimp (Map.remove term result) constant xs
                            | upd -> makeSimp (Map.update result term upd) constant xs

            // Once the dictionary (Map) has been created, all we need to do is convert it into a list of terms, thus
            // satisfying our definition of a SumPow sum.

            let result =
                let terms = mapTerm' flattenTerm sum

                match makeSimp Map.empty (Const Zero) terms with
                | Zero, dict -> dict
                | cst, dict -> Map.add [ powId (simpPureConst cst) ] (Const One) dict

            if Map.isEmpty result then Const Zero else

            result
            |> Map.toList
            |> List.map (
                Term
                << function
                    | key, One -> flattenTerm key
                    | key, value -> flattenTerm (powId value :: key))
            |> Sum
        //  |> flatten

        /// Performs a basic simplification of the given expression by combining like terms and reducing powers. This also
        /// applies to function arguments. It does not perform full distribution or factorization. It only reduces terms and
        /// powers recursively. This function might throw an exception if a fixed point has not been found.
        let rec public simplify =

            // The simplification algorithm may not simplify everything on the first try, so we give it a maximum
            // of 5 chances to repeat itself (after which it throws an exception). In general, based on observation,
            // the fixed point is found in just one or two iterations. If the maximum fixed point is reached, this most
            // certainly indicates that there is a problem somewhere in the implementation (hence the need to throw an
            // exception, as this is not expected behavior).

            FixedPoint.tryFixedPoint 5 //>> memoize
            <| function
                | PureConstantExpression.PureConstantExpression cst -> simpPureConst cst
                | Name _ as name -> name

                | Power (b, One) -> simplify b
                | Power (_, Zero) -> Const One
                | Frac (num, den) -> simpFrac num den

                | Sum xs -> simpSum xs

                | Fun(name, args) -> Fun(name, List.map simplify args)
                | other -> other

        /// Simplify the given expression after developing it to the maximum possible extent.
        let public expandAndSimplify =
            Expand.fullExpand >> Simplification.simplify

        /// Expand the given expression to the maximum possible extent after simplifying it.
        let public simplifyAndExpand =
            Simplification.simplify >> Expand.fullExpand

    /// Development (distributivity of sum and product) of SumPow algebraic expressions.
    [<RequireQualifiedAccess>]
    module public Expand =
        open ElementaryOperations
        open SimplifiedSum

        /// Implements Newton's binomial for `(x + y)^n`. Takes the two sum terms and the integer exponent and returns
        /// the resulting sum. See https://en.wikipedia.org/wiki/Binomial_theorem.
        let private newtonBinomial (x: Pow list) (y: Pow list) (n: int) =
            let spn = Const n

            let binomialTerm (k: int) =
                let spk = Const k
                let bin = Const(binomial n k)

                powId bin
                :: List.map (function Pow(b, p) -> power' (expand b, expand p * (spn - spk))) x
                 @ List.map (function Pow(b, p) -> power' (expand b, expand p * spk)) y
                |> Simplification.basicTermSimp
                |> Flatten.flattenTerm
                |> Term

            Sum [ for k = 0 to n do binomialTerm k ]

        /// Implements the generalized binomial theorem for `(x₁ + x₂ + ⋅⋅⋅ + xₘ)^n`.
        /// See https://en.wikipedia.org/wiki/Multinomial_theorem.
        let private newtonMultinomial (xs: Term list) (n: int) =

            /// Generates the list of powers that will be involved in the final sum.
            let rec inner start currentSum currentCombination combinations =
                if List.length currentCombination = List.length xs then
                    if currentSum = n then currentCombination :: combinations
                    else combinations
                else
                    if currentSum > n then combinations
                    else
                        let folder acc i = inner (start + 1) (currentSum + i) (i :: currentCombination) acc
                        List.fold folder combinations [ 0 .. (n - currentSum) ]

            /// The list of powers that will be involved in the final sum.
            let exponentVectors = inner 0 0 [] []

            let multinomialTerm (vec: int list) =
                let mul = Const(multinomial vec)
                let folder acc p term =  acc * power (sumId term, Const (int p))
                List.fold2 folder mul vec xs

            Sum (manyTermId (List.map multinomialTerm exponentVectors))

        /// Multiply the two powers (symbolized by tuples), taking distributivity into account.
        /// Returns a power in the same form.
        let rec private distribute =
            function
            | SimpleSP x, SimpleSP y -> x * y

            | Power(x, One), y -> distribute (x, y)
            | x, Power(y, One) -> distribute (x, y)

            | Sum xs, SimpleSP y
            | SimpleSP y, Sum xs ->
                let y = powId y
                Sum (mapTerm' (fun t -> y :: t) xs)

            | SimplifiedSum xs, SimplifiedSum ys ->
                // Distributivity has Cartesian product symmetries (in the Reals field).
                let cp = cartProd [ xs; ys ]
                let ss = List.fold (fun acc a -> List.flatten a :: acc) [] cp
                simplifiedSumToSum ss

            | a, b -> a * b

        /// Expand a sum or product power.
        let private expandPow =
            function
            | Prod xs, p -> Sum [ Term(List.map (fun (b, p') -> power'(expand b, expand p' * p)) xs) ], Const One
            | Sum [ Term x; Term y ], PureConstantExpression.PureConstantExpressionInteger p when p > 0 -> newtonBinomial x y p, Const One
            | Sum terms, PureConstantExpression.PureConstantExpressionInteger p when p > 0 -> newtonMultinomial terms p, Const One
            | b, p -> expand b, expand p

        /// Expand a product.
        let private expandTerm (term: (SumPow * SumPow) list) =
            let (x :: xs) = List.map expandPow term
            List.fold (fun acc (b, p) -> distribute (acc, (b ** p))) (power x) xs

        /// Expands the given expression.
        let public expand =
            function
            | SimpleSP x -> x
            | Power(b, p) -> power (expandPow (b, p))
            | Prod prod -> expandTerm prod
            | SimplifiedSum ss -> Sum (manyTermId (List.map expandTerm ss))
            | other -> other

        /// Apply expansion until a fixed point. Might throw an exception if a fixed point is not found.
        let public fullExpand = FixedPoint.tryFixedPoint 20 expand

    /// A module for making substitutions in SumPow.
    module public Subst =
        open SimplifiedSum
        open System.Collections.Generic

        /// Replaces the variable (`Name string`) with the given expression.
        let rec public substVar (name: string) (sub: SumPow) =
            function
            | Name name' when name = name' -> sub
            | Fun(fname, args) -> Fun(fname, List.map (substVar name sub) args)
            | Sum xs -> Sum(mapPow' (fun b p -> Pow(substVar name sub b, substVar name sub p)) xs)
            | remains -> remains

        /// Replaces the variables (many `Name string`) with the associated expressions.
        let public manySubstVar (pairs: Dictionary<string, SumPow>) (expr: SumPow) =

            let rec inner =
                function
                | Name name' ->
                    match pairs.TryGetValue name' with
                    | true, sub -> sub
                    | _ -> Name name'

                | Fun(fname, args) -> Fun(fname, List.map inner args)
                | Sum xs -> Sum(mapPow' (fun b p -> Pow(inner b, inner p)) xs)
                | remains -> remains

            inner expr

    /// A module that implements the evaluation of elementary functions.
    [<RequireQualifiedAccess>]
    module public InternalFunction =

        type public InternalFunction =
            | Pow of base': SumPow * exp: SumPow
            | Root of base': SumPow * exp: SumPow option // default: Sqrt
            | Log of arg: SumPow * base': SumPow option // default: Ln
            | Exp of arg: SumPow
            | Sin of arg: SumPow
            | Cos of arg: SumPow
            | Tan of arg: SumPow
            | Csc of arg: SumPow
            | Sec of arg: SumPow
            | Cot of arg: SumPow
            | ArSin of arg: SumPow
            | ArCos of arg: SumPow
            | ArTan of arg: SumPow
            | ArCsc of arg: SumPow
            | ArSec of arg: SumPow
            | ArCot of arg: SumPow
            | Sinh of arg: SumPow
            | Cosh of arg: SumPow
            | Tanh of arg: SumPow
            | Csch of arg: SumPow
            | Sech of arg: SumPow
            | Coth of arg: SumPow
            | ArSinh of arg: SumPow
            | ArCosh of arg: SumPow
            | ArTanh of arg: SumPow
            | ArCsch of arg: SumPow
            | ArSech of arg: SumPow
            | ArCoth of arg: SumPow
            | Sinc of arg: SumPow
            | Abs of arg: SumPow

        let public (|InternalFunction|_|) =
            function
            | Fun("Pow", [ base'; exp ]) -> Some(InternalFunction.Pow(base', exp))
            | Fun("Root", [ base'; exp ]) -> Some(InternalFunction.Root(base', Some exp))
            | Fun("Sqrt", [ arg ]) -> Some(InternalFunction.Root(arg, None))
            | Fun("Log", [ arg; base' ]) -> Some(InternalFunction.Log(arg, Some base'))
            | Fun("Log", [ arg ]) -> Some(InternalFunction.Log(arg, None))
            | Fun("Exp", [ arg ]) -> Some(InternalFunction.Exp arg)
            | Fun("Sin", [ arg ]) -> Some(InternalFunction.Sin arg)
            | Fun("Cos", [ arg ]) -> Some(InternalFunction.Cos arg)
            | Fun("Tan", [ arg ]) -> Some(InternalFunction.Tan arg)
            | Fun("Csc", [ arg ]) -> Some(InternalFunction.Csc arg)
            | Fun("Sec", [ arg ]) -> Some(InternalFunction.Sec arg)
            | Fun("Cot", [ arg ]) -> Some(InternalFunction.Cot arg)
            | Fun("ArSin", [ arg ]) -> Some(InternalFunction.ArSin arg)
            | Fun("ArCos", [ arg ]) -> Some(InternalFunction.ArCos arg)
            | Fun("ArTan", [ arg ]) -> Some(InternalFunction.ArTan arg)
            | Fun("ArCsc", [ arg ]) -> Some(InternalFunction.ArCsc arg )
            | Fun("ArSec", [ arg ]) -> Some(InternalFunction.ArSec arg )
            | Fun("ArCot", [ arg ]) -> Some(InternalFunction.ArCot arg )
            | Fun("Sinh", [ arg ]) -> Some(InternalFunction.Sinh arg)
            | Fun("Cosh", [ arg ]) -> Some(InternalFunction.Cosh arg)
            | Fun("Tanh", [ arg ]) -> Some(InternalFunction.Tanh arg)
            | Fun("Csch", [ arg ]) -> Some(InternalFunction.Csch arg)
            | Fun("Sech", [ arg ]) -> Some(InternalFunction.Sech arg)
            | Fun("Coth", [ arg ]) -> Some(InternalFunction.Coth arg)
            | Fun("ArSinh", [ arg ]) -> Some(InternalFunction.ArSinh arg)
            | Fun("ArCosh", [ arg ]) -> Some(InternalFunction.ArCosh arg)
            | Fun("ArTanh", [ arg ]) -> Some(InternalFunction.ArTanh arg)
            | Fun("ArCsch", [ arg ]) -> Some(InternalFunction.ArCsch arg)
            | Fun("ArSech", [ arg ]) -> Some(InternalFunction.ArSech arg)
            | Fun("ArCoth", [ arg ]) -> Some(InternalFunction.ArCoth arg)
            | Fun("Sinc", [ arg ]) -> Some(InternalFunction.Sinc arg)
            | Fun("Abs", [ arg ]) -> Some(InternalFunction.Abs(arg))
            | _ -> None

        let inline public evaluate (spEval: SumPow -> Constant) =
            function
            | InternalFunction.Pow(base', exp) -> spEval base' ** spEval exp
            | InternalFunction.Root(base', None) -> mapf sqrt (spEval base')
            | InternalFunction.Root(base', Some exp) -> spEval base' ** (One / spEval exp)
            | InternalFunction.Log(arg, None) -> mapf log (spEval arg)
            | InternalFunction.Log(arg, Some base') -> mapf log (spEval arg) / mapf log (spEval base')
            | InternalFunction.Sin(arg) -> mapf sin (spEval arg)
            | InternalFunction.Exp(arg) -> mapf exp (spEval arg)
            | InternalFunction.Cos(arg) -> mapf cos (spEval arg)
            | InternalFunction.Tan(arg) -> mapf tan (spEval arg)
            | InternalFunction.Csc(arg) -> mapf (fun x -> 1.0 / sin x) (spEval arg)
            | InternalFunction.Sec(arg) -> mapf (fun x -> 1.0 / cos x) (spEval arg)
            | InternalFunction.Cot(arg) -> mapf (fun x -> 1.0 / tan x) (spEval arg)
            | InternalFunction.ArSin(arg) -> mapf asin (spEval arg)
            | InternalFunction.ArCos(arg) -> mapf acos (spEval arg)
            | InternalFunction.ArTan(arg) -> mapf atan (spEval arg)
            | InternalFunction.ArCsc(arg) -> mapf (fun x -> 1.0 / asin x) (spEval arg)
            | InternalFunction.ArSec(arg) -> mapf (fun x -> 1.0 / acos x) (spEval arg)
            | InternalFunction.ArCot(arg) -> mapf (fun x -> 1.0 / atan x) (spEval arg)
            | InternalFunction.Sinh(arg) -> mapf sinh (spEval arg)
            | InternalFunction.Cosh(arg) -> mapf cosh (spEval arg)
            | InternalFunction.Tanh(arg) -> mapf tanh (spEval arg)
            | InternalFunction.Csch(arg) -> mapf (fun x -> 1.0 / sinh x) (spEval arg)
            | InternalFunction.Sech(arg) -> mapf (fun x -> 1.0 / cosh x) (spEval arg)
            | InternalFunction.Coth(arg) -> mapf (fun x -> 1.0 / tanh x) (spEval arg)
            | InternalFunction.ArSinh(arg) -> mapf (fun x -> log (sqrt (pown x 2 + 1.0) + x)) (spEval arg)
            | InternalFunction.ArCosh(arg) -> mapf (fun x -> log (x + sqrt (x - 1.0) * sqrt (x + 1.0))) (spEval arg)
            | InternalFunction.ArTanh(arg) -> mapf (fun x -> 0.5 * log (x + 1.0) - 0.5 * log (1.0 - x)) (spEval arg)
            | InternalFunction.Sinc(arg) -> mapf (fun x -> sin x / x) (spEval arg)
            | InternalFunction.Abs(arg) -> mapf abs (spEval arg)
            | other -> failwithf "Not implemented: %A" other

    /// A module for elementary functions (see https://en.wikipedia.org/wiki/Elementary_function).
    module public ElemFun =
        open ElementaryOperations
        open Complex

        /// An active pattern that matches either `Exp[arg]` or `e**arg`.
        let public (|Exp|_|) =
            function
            | Power(Name "e", p) -> Some p
            | Fun("Exp", [ arg ]) -> Some arg
            | _ -> None

        let public (|Log|_|) =
            function
            | Fun("Log", [ x; b ]) -> Some (x, b)
            | Fun("Log", [ x ]) -> Some (x, Const 10)
            | Fun("Ln", [ x ]) -> Some (x, Const Math.E)
            | _ -> None

        let public (|Sin|_|) =
            function
            | Fun("Sin", [ x ]) -> Some x
            | _ -> None

        let public (|Cos|_|) =
            function
            | Fun("Cos", [ x ]) -> Some x
            | _ -> None

        let public (|Root|_|) =
            function
            | Fun("Root", [ arg; expn ]) -> Some (arg, expn)
            | Fun("Sqrt", [ arg ]) -> Some (arg, Const 2)
            | Power (arg, Frac (num, den)) -> Some (Simplification.simplify (arg ** num), den)
            | _ -> None

    /// A module for the approximate numerical evaluation of SumPow expressions.
    module public NumericEvaluation =
        open System.Linq
        open System.Collections.Generic

        exception public UnboundVariableException of vname: string
        exception public UnboundFunctionException of fname: string

        /// Determine whether the two expressions are numerically approximately equal up to the given precision. If `eps` is `None`
        /// then the comparison is made with a fixed femto-precision (`1e-15`).
        let public approximatelyEquals (sp1: SumPow) (sp2: SumPow) (values: Dictionary<string, Constant>) (eps: double option) =
            Constant.approximatelyEquals (evaluate sp1 values) (evaluate sp2 values) eps

        /// Determine whether the given expressions is numerically approximately equal to zero up to the given precision.
        /// If `eps` is `None` then the comparison is made with a fixed femto-precision (`1e-15`).
        let public approximatelyEqualsZero (sp: SumPow) (eps: double option) =
            approximatelyEquals sp (Const Zero) (Dictionary []) eps

        /// Evaluates the given expression by replacing each variable found with its given value. Note: The calculation is
        /// subject to `double` capabilities. This function might throw an exception if some variables are not assigned.
        let public evaluate (sp: SumPow) (values: Dictionary<string, Constant>) =

            let rec inner =
                function

                // Common constants
                | Name "pi"  | Name "π" -> Constant 3.141592653589793 // pi  π
                | Name "e"   | Name "E" -> Constant 2.718281828459045 // e   E
                | Name "tau" | Name "τ" -> Constant 6.283185307179586 // tau τ
                | Name "phi" | Name "φ" -> Constant 1.618033988749895 // phi φ

                // Variables are replaced by their associated values
                | Name name ->
                    match values.TryGetValue name with
                    | true, constant -> constant
                    | _ -> raise (UnboundVariableException name)

                | Const cst -> cst
                | Frac(a, b) -> inner a / inner b
                | Power(b, p) -> inner b ** inner p
                | Sum xs -> List.fold (fun acc a -> acc + evalTerm a) Zero xs
                | InternalFunction.InternalFunction f -> InternalFunction.evaluate inner f
                | Fun(fname, _) -> raise (UnboundFunctionException fname)

            and evalTerm (Term prod) = List.fold (fun acc a -> acc * evalPow a) One prod
            and evalPow (Pow(b, p)) = inner b ** inner p

            inner sp

        /// Assuming the expression contains only constants, returns the approximate result of the expression.
        let public evaluate0 (sp: SumPow) =
            evaluate sp (Dictionary [])

        /// Assuming that the expression contains only one variable, return the result of the constant expression
        /// approximated, replacing the variable with the given value.
        let inline public evaluate1 (sp: SumPow) (variable: string) (value: Constant) =
            evaluate sp (Dictionary(dict [ variable, value ]))

        /// Generates an array of Constant numerical values from `min` to `max` in `step` increments.
        let public generatePoints1D (min: double) (max: double) (step: double) (sp: SumPow) (variable: string) =
            let xs = [| Constant min .. Constant step .. Constant max |]
            Array.Parallel.map (evaluate1 sp variable) xs

        /// Generates an array of constant numeric 2D points from `min` to `max` in `step` increments.
        /// Each new array corresponds to a new part of the graph separated by an asymptote.
        let public generatePoints2D' (min: double) (max: double) (step: double) (sp: SumPow) (variable: string) =
            let xs = [| Constant min .. Constant step .. Constant max |]
            let xs = Array.Parallel.map (function (Constant x) -> if Constant.approximatelyEquals x (Constant 0) None then Constant 0. else Constant x) xs
            let ys = Array.Parallel.map (evaluate1 sp variable) xs
            let points = Array.zip xs ys

            let splitByAsymptots values =
                values
                |> Array.fold
                    (fun (acc: ResizeArray<ResizeArray<_>>) (Constant x, Constant y) ->
                        let currentList = acc.[acc.Count - 1]
                        let (_, lasty) = currentList.LastOrDefault((x, y))

                        if (abs (y / lasty) > 1. / step)
                        then acc.Add(new ResizeArray<_>())
                        else currentList.Add(x, y)

                        acc)
                    (ResizeArray<ResizeArray<_>>(seq [ ResizeArray<_>() ]))
                |> Seq.map (fun sublist -> sublist.ToArray())
                |> Seq.toArray

            splitByAsymptots points

        /// Generates an array of Constant numerical 2D points from `min` to `max` in `step` increments.
        let public generatePoints2D (min: double) (max: double) (step: double) (sp: SumPow) (variable: string) =
            let xs = [| Constant min .. Constant step .. Constant max |]
            let ys = Array.Parallel.map (evaluate1 sp variable) xs
            Array.zip xs ys |> Array.filter (function Constant x, Constant y -> Double.IsFinite y)

        /// If the given expression contains variables, then evaluate only the constant numeric terms.
        /// For example `3x/4 - 1` will give `0.75x - 1`.
        let rec public partialEval (sp: SumPow) =

            ()

    /// Extends the field of reals (modeled by SumPow) to the field of complexes.
    module public Complex =
        open SimplifiedSum
        open ElemFun

        /// The variable used to represent the imaginary unit is `Name "i"`.
        let private imaginaryUnitNotation = Name "i"

        /// Matches an expression of the form `Cos[x] + iSin[x]` ≡ `Exp[i*x]` where `i` is the imaginary unit.
        let public (|Cis|_|) =
            function

            // Cis[x]
            | Fun("Cis", [ arg ]) -> Some arg

            // Exp[i*x]
            | Exp(ProdWith1 isImaginaryUnit prod) -> Some (Misc.prodToSumPow prod)

            // Cos[x] + iSin[x]
            | SimplifiedSum [ [ Cos x, One ]; [ (ImaginaryUnit, PureConstantExpression.PureConstantExpressionInteger n); Sin x', One ] ]
            | SimplifiedSum [ [ Cos x, One ]; [ Sin x', One ; (ImaginaryUnit, PureConstantExpression.PureConstantExpressionInteger n)] ]
            | SimplifiedSum [ [ Sin x', One; (ImaginaryUnit, PureConstantExpression.PureConstantExpressionInteger n) ]; [ Cos x, One ] ]
            | SimplifiedSum [ [ (ImaginaryUnit, PureConstantExpression.PureConstantExpressionInteger n); Sin x', One ]; [ Cos x, One ] ]
                when (x = x') && ((n % 4) = 1) -> Some x

            | _ -> None

        /// Matches an expression that reduces to the imaginary unit. The expression `Sqrt[-1]` is a dangerous abuse
        /// of notation that is not implemented as a representation of `i`.
        let public (|ImaginaryUnit|_|) =
            function

            // Trivial case: i = i.
            | i when i = imaginaryUnitNotation -> Some ()

            // i^(4n + 1) ≡ i
            | Power (ImaginaryUnit, PureConstantExpression.PureConstantExpressionInteger n) when (n % 4) = 1 -> Some ()

            // Cis[pi/2] ≡ Cos[pi/2] + iSin[pi/2] ≡ Exp[iπ/2] ≡ i
            | Cis (Frac (Name "pi", PureConstantExpression.PureConstantExpressionInteger 2)) -> Some ()

            | _ -> None

        /// Check whether the given expression corresponds to the imaginary unit `i`.
        let public isImaginaryUnit =
            function
            | ImaginaryUnit _ -> true
            | _ -> false

        [<Struct; RequireQualifiedAccess>]
        type public ComplexSumPow =

            /// Complex expression of the form `z = a + ib`
            | VectorForm of re: SumPow * im: SumPow

            /// Complex expression of the form `z(r, ϑ) = r⋅Exp[iϑ]` where `r` is the radius and `ϑ` is the angle.
            | PolarForm of radius: SumPow * angle: SumPow

            static member op_Addition(a: ComplexSumPow, b: ComplexSumPow) = complexAddition (a, b)
            static member op_Subtraction(a: ComplexSumPow, b: ComplexSumPow) = complexSubtraction (a, b)
            static member op_Multiply(a: ComplexSumPow, b: ComplexSumPow) = complexMultiplication (a, b)
            static member op_Division(a: ComplexSumPow, b: ComplexSumPow) = complexDivision (a, b)
            static member op_UnaryNegation(a: ComplexSumPow) = complexNegation a

        let private convertToVectorForm =
            function
            | ComplexSumPow.VectorForm _ as z -> z
            | ComplexSumPow.PolarForm(radius, angle) ->
                ComplexSumPow.VectorForm(radius * Fun("Cos", [ angle ]), radius * Fun("Sin", [ angle ]))

        let private convertToPolarForm =
            function
            | ComplexSumPow.PolarForm _ as z -> z
            | _ -> failwith "todo."

        let private complexAddition =
            function
            | ComplexSumPow.VectorForm (re1, im1), ComplexSumPow.VectorForm (re2, im2) ->
                ComplexSumPow.VectorForm (re1 + re2, im1 + im2)

            | ComplexSumPow.PolarForm (radius1, angle1), ComplexSumPow.PolarForm (radius2, angle2) when angle1 = angle2 ->
                ComplexSumPow.PolarForm (radius1 + radius2, angle1)
            
            | z1, z2 -> convertToVectorForm z1 + convertToVectorForm z2

        let private complexSubtraction =
            function
            | ComplexSumPow.VectorForm (re1, im1), ComplexSumPow.VectorForm (re2, im2) ->
                ComplexSumPow.VectorForm (re1 - re2, im1 - im2)

            | ComplexSumPow.PolarForm (radius1, angle1), ComplexSumPow.PolarForm (radius2, angle2) when angle1 = angle2 ->
                ComplexSumPow.PolarForm (radius1 - radius2, angle1)
            
            | z1, z2 -> convertToVectorForm z1 - convertToVectorForm z2

        let private complexMultiplication =
            function
            | ComplexSumPow.VectorForm(re1, im1), ComplexSumPow.VectorForm(re2, im2) ->
                ComplexSumPow.VectorForm(re1 * re2 - im1 * im2, re1 * im2 + im1 * re2)

            | ComplexSumPow.PolarForm(radius1, angle1), ComplexSumPow.PolarForm(radius2, angle2) ->
                ComplexSumPow.PolarForm(radius1 * radius2, angle1 + angle2)

            | z1, z2 -> convertToVectorForm z1 * convertToVectorForm z2

        let private complexDivision =
            function
            | ComplexSumPow.VectorForm(re1, im1), ComplexSumPow.VectorForm(re2, im2) ->
                ComplexSumPow.VectorForm(re1 * re2 - im1 * im2, re1 * im2 + im1 * re2)

            | ComplexSumPow.PolarForm(radius1, angle1), ComplexSumPow.PolarForm(radius2, angle2) ->
                ComplexSumPow.PolarForm(radius1 / radius2, angle1 - angle2)

            | z1, z2 -> convertToPolarForm z1 / convertToPolarForm z2

        let private complexNegation = function
            | ComplexSumPow.VectorForm(re, im) -> ComplexSumPow.VectorForm(-re, -im)
            | ComplexSumPow.PolarForm(radius, angle) -> ComplexSumPow.PolarForm(-radius, angle)

        let inline private justRe x = ComplexSumPow.VectorForm(x, Const Zero)
        let inline private justIm x = ComplexSumPow.VectorForm(Const Zero, x)
        let inline private complex re im = ComplexSumPow.VectorForm(re, im)

        let private expnImg (n: int) =
            match n % 4 with
            | 0 -> Const 1
            | 1 -> imaginaryUnitNotation
            | 2 -> Const -1
            | 3 -> -imaginaryUnitNotation
            | _ -> failwith "Unexpected case"

        let private complexProduct (prod: (SumPow * SumPow) list) =
            let im, re = List.partition (fst >> isImaginaryUnit) prod
            let im1, im2 = List.partition (snd >> Misc.isPureConstInteger) im
            let (Const (CInteger p)) = List.fold ( + ) (Const Zero) (List.map snd im1)
            let im1 = expnImg p
            let re = Misc.prodToSumPow re
            let im =  Misc.prodToSumPow ((im1, Const One) :: im2)

            complex re im

        let public asComplex =
            function
            | Fun("Complex", [ re; im ]) -> complex re im
            | Cis arg -> complex arg arg
            | ImaginaryUnit -> justIm (Const One)
            | SimpleSP x -> justRe x
            | Power(ImaginaryUnit, PureConstantExpression.PureConstantExpressionInteger n) -> asComplex (expnImg n)
            | Prod prod -> complexProduct prod

        let public asSumPow (z: ComplexSumPow) =
            let (ComplexSumPow.VectorForm(re, im)) = convertToVectorForm z
            re + (imaginaryUnitNotation * im)

    [<RequireQualifiedAccess>]
    module public ModularArithmetic =
        open ElementaryOperations

        exception public NumberHaveNotTheSameModulus of ModularNumber list

        [<Struct; Symbolic>]
        type public ModularNumber =
            { number: SumPow
              modulus: int }
            
            static member op_Addition(a: ModularNumber, b: ModularNumber) = addition a b
            static member op_Subtraction(a: ModularNumber, b: ModularNumber) = subtraction a b
            static member op_Multiply(a: ModularNumber, b: ModularNumber) = multiplication a b
            static member op_Division(a: ModularNumber, b: ModularNumber) = division a b
            static member Pow(a: ModularNumber, b: ModularNumber) = power a b
            static member op_UnaryNegation(a: ModularNumber) = { a with number = -a.number }

            interface ISymbolic with
                member this.ToSymbolic() = toSymbolic this
                member this.ToLatex() = Some (toLatex this)
                member this.ToLatexOrString() = string this
                member this.Hash = hash (toSumPow this)

        let private toLatex { number = number; modulus = modulus } =
            sprintf @"\left(%s\right)\;\left(\text{mod}\;%d\right)" (toLatexValue number) modulus

        let private toSymbolic { number = number; modulus = modulus } =
            let snum = Atomic.toSymbolic number
            let smod = atom (Atomic.Const modulus)

            { atom = Atom.Identifier "ModularNumber"
              attributes = [ ("number", snum); ("modulus", smod) ] }

        let private toSumPow { number = number; modulus = modulus } =
            if Misc.isZero number then Const Zero
            else Fun("ModularNumber", [ number; Const (double modulus) ])

        let inline private congruence { number = number; modulus = modulus } =
            match number with
            | PureConstantExpression.PureConstantExpressionInteger number -> { number = Const (double (number % modulus)); modulus = modulus }
            | number -> { number = number; modulus = modulus }

        let public (|ModularNumber|_|) =
            function
            | Fun("ModularNumber", [ number; PureConstantExpression.PureConstantExpressionInteger modulus ]) ->
                Some (congruence { number = number; modulus = modulus })
            | _ -> None

        let private binOp f ({ number = a; modulus = m1 } as n1) ({ number = b; modulus = m2 } as n2) =
            if m1 <> m2 then
                raise (NumberHaveNotTheSameModulus [ n1; n2 ])

            congruence { number = modulo (f a b, Const m1); modulus = m1 }

        let public modularNumber = toSumPow

        let private addition = binOp ( + )
        let private subtraction = binOp ( - )
        let private multiplication = binOp ( * )
        let private division = binOp ( / )
        let private power = binOp ( ** )

    /// A module containing miscellaneous SumPow functions.
    [<RequireQualifiedAccess>]
    module public Misc =
        open PureConstantExpression
        open SimplifiedSum
        open ElementaryOperations

        /// Checks if the given expression is a pure constant (contains no `Name string`).
        let public isPureConst =
            function
            | PureConstantExpression _ -> true
            | _ -> false

        let public isPureConstInteger =
            function
            | PureConstantExpressionInteger _ -> true
            | _ -> false

        let public isIntegerRational =
            function
            | Frac(PureConstantExpressionInteger _, PureConstantExpressionInteger _) -> true
            | PureConstantExpressionInteger _ -> true
            | _ -> false

        /// Check whether the given expression reduces to 0.
        let public isZero =
            function
            | Zero -> true
            | _ -> false

        /// Check whether the given expression reduces to 1.
        let public isOne =
            function
            | One -> true
            | _ -> false

        /// Check whether the given expression is a fraction (with non-unity denominator).
        let public isFrac =
            function
            | Frac _ -> true
            | _ -> false

        /// Check that the given expression is a root.
        let public isRoot =
            function
            | ElemFun.Root _ -> true
            | _ -> false

        /// Convert the product representation into SumPow.
        let public prodToSumPow (prod: (SumPow * SumPow) list) =
            List.map power' prod |> Term |> sumId

        /// Check whether the given expression is a sum (can contain a single element.).
        let public isSum =
            function
            | Sum xs -> List.length xs > 1
            | _ -> false

        /// Lists the syntactic variables present in the given expression.
        let public listVariables (expr: SumPow) =

            let rec inner (result: string Set) =
                function
                | Name name -> Set.add name result
                | Fun(_, args) -> List.fold inner result args
                | SimplifiedSum.SimplifiedSum xs ->
                    let go (b, p) = Set.union (inner result b) (inner result p)
                    SimplifiedSum.mapPowFlatten go xs |> Set.unionMany
                | _ -> result

            inner Set.empty expr |> Set.toList

        /// Recursively transforms each `Root[x, nth]` of the given expression into `x^(1/nth)`.
        let rec public convertAllRootsToPower =
            function
            | ElemFun.Root(x, PureConstantExpressionInteger nth) -> (convertAllRootsToPower x) ** (1 / Const nth)
            | Power(b, p) -> convertAllRootsToPower b ** convertAllRootsToPower p
            | Fun(fname, args) -> Fun(fname, List.map convertAllRootsToPower args)
            | SumList xs -> Sum (manyTermId (List.map convertAllRootsToPower xs))
            | other -> other

        /// Recursively transforms each `x^(1/nth)` of the given expression into `Root[x, nth]`.
        let rec public convertAllRationalPowersToRoot =
            function
            | Power(b, PureConstantExpressionRational(num, den)) -> Fun("Root", [ b ** num; Const den ])
            | ElemFun.Root(x, PureConstantExpressionInteger nth) -> Fun("Root", [ x; Const nth ])
            | Power(b, p) -> convertAllRationalPowersToRoot b ** convertAllRationalPowersToRoot p
            | Fun(fname, args) -> Fun(fname, List.map convertAllRationalPowersToRoot args)
            | SumList xs -> Sum (manyTermId (List.map convertAllRationalPowersToRoot xs))
            | other -> other
