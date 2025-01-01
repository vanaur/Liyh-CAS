namespace Liyh.Kernel

#nowarn "40"    // This warning is activated for the memoized function `simplify` for the active pattern "One".
#nowarn "3391"  // The implicit conversion of an integer into a bigint causes a warning.
#nowarn "25"    // Incomplete pattern-matchings raise warnings (rightly so, but sometimes this is not encountered at runtime).
#nowarn "57"    // Preview features.

[<AutoOpen>]
module rec SumPow =
    open System
    open System.Runtime.CompilerServices
    open Liyh.Utils
    open Liyh.Kernel
    open MathRender

    exception public UnknownSumPowExpressionException of SumPow

    /// This module consists of fundamental building `Sum`'s blocks that take into account the flattening of expressions.
    /// These functions should be called every time a sum / term or power is constructed.
    [<AutoOpen>]
    module public PowId =
        open PureConstantExpression

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
            | Term [ Pow(b, One) ] -> b
            | Term [ Pow(Sum [ term ], One) ] -> sumId term
            | Term [ Pow((PureConstantExpressionInteger _ as b) 
                        ,(PureConstantExpressionInteger _ as p)) ] -> b ** p
            | term -> Sum [ term ]

    /// Various active patterns useful for working around SumPow.
    [<AutoOpen>]
    module public Pattern =
        open ElementaryOperations
        open PureConstantExpression

        /// An active pattern that represents either a variable (`Name _`), a pure constant (`PureConstantExpression _`) or a
        /// function (`Fun _`). In other words, it's not a sum, a product or a power.
        let public (|SimpleSP|_|) =
            function
            | Name _ as a -> Some a
            | PureConstantExpression _ as a -> Some a   
            | Fun _ as a -> Some a
            | _ -> None

        /// An active pattern that matches the divide-by-zero symbol.
        let public (|DivByZero|_|) =
            function
            | Fun("DivByZero", _) as sp -> Some sp
            | _ -> None

        /// An active pattern that matches the pure constant expression which reduces to the integer 0.
        let public (|Zero|_|) =

            let matcher =
                function
                | PureConstantExpressionInteger 0 -> Some()
                | _ -> None

            // Many similar calls should be made to this active-pattern, in the interests of general
            // performance we can memoize the result.
            memoize matcher

        /// An active pattern that matches the pure constant expression which reduces to the integer 0.
        /// This active pattern use the EqualityTest heuristic.
        let public (|Zero'|_|) (sp: SumPow) =
            if EqualityTest.equalsZero sp then Some() else None

        /// An active pattern that matches the pure constant expression which reduces to the integer 1.
        let public (|One|_|) =

            let matcher =
                function
                | PureConstantExpressionInteger 1 -> Some()
                | _ -> None

            // Many similar calls should be made to this active-pattern, in the interests of general
            // performance we can memoize the result.
            memoize matcher

        /// An active pattern that matches the pure constant expression which reduces to the integer -1.
        let public (|NegOne|_|) =
            function
            |   PureConstantExpressionInteger -1 -> Some()
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
            | [] -> None
            // | [ _ ] -> None
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
        let public (|ProdWith|_|) (pred: SumPow -> bool) (sp: SumPow) =

            // Just return the unit of multiplication when the product only contains the term to be matched.
            let punit = (Const One, Const One)

            match sp with
            | Prod [ p ] when pred (power p) -> Some ([ punit ], 1)
            | Prod xs ->
                match List.partition (fun p -> pred (power p)) xs with
                | [], _ -> None
                | ts, xs' ->
                    let res = if List.isEmpty xs' then [ punit ] else xs'
                    Some(res, List.length ts)
            | _ -> None

        /// An active pattern that matches a sum that contains the given expression at least once. In case of Some,
        /// returns a tuple `Sum (sum, n)` where `sum` is the sum expression list without the the expression to
        /// be found and where `n` is the number of time it appears.
        let public (|SumWith|_|) (pred: SumPow -> bool) (sp: SumPow) =

            // Just return the unit of summation when the sum only contains the term to be matched. 
            let sunit = (Const Zero)

            match sp with
            | SimplifiedSum.SumList [ term ] when pred term -> Some ([ sunit ], 1) // Just return the unit of the sum
            | SimplifiedSum.SumList xs ->
                match List.partition pred xs with
                | [], _ -> None
                | ts, xs' ->
                    let res = if List.isEmpty xs' then [ sunit ] else xs'
                    Some(res, List.length ts)
            | _ -> None

        /// An active pattern that matches a product that contains exactly once the given expression. In case of Some,
        /// returns product expression list without the the expression to be found.
        let public (|ProdWith1|_|) (pred: SumPow -> bool) =
            function
            | ProdWith pred (prod, 1) -> Some prod
            | _ -> None

        /// An active pattern that matches a product that contains the given expression at least once. In case of Some,
        /// returns a tuple `Prod (p, prod, n)` where `prod` is the product expression list without the the expression to
        /// be found, where `n` is the number of time it appears and `p` being the matched predicate.
        let public (|ProdWithKeep|_|) (pred: SumPow -> bool) =
            function
            | Prod [ p ] when pred (power p) -> Some ([ power p ], [ (Const One, Const One) ], 1)
            | Prod xs ->
                match List.partition (fun p -> pred (power p)) xs with
                | [], _ -> None
                | ts, [] -> Some(List.map power ts, [ (Const One, Const One) ], List.length ts)
                | ts, xs' -> Some(List.map power ts, xs', List.length ts)
            | _ -> None

        /// An active pattern that matches a product that contains exactly once the given expression. In case of Some,
        /// returns product expression list including the the expression to be found.
        let public (|ProdWith1Keep|_|) (pred: SumPow -> bool) =
            function
            | ProdWithKeep pred (p, prod, 1) -> Some (List.exactlyOne p, prod)
            | _ -> None

        /// An active pattern that matches a sum that contains exactly once the given expression. In case of Some,
        /// returns sum expression list without the the expression to be found.
        let public (|SumWith1|_|) (pred: SumPow -> bool) =
            function
            | SumWith pred (sum, 1) -> Some sum
            | _ -> None

        /// Match an expression that reduce to a product with a negative number. The return value consists of a tuple
        /// containing the absolute value of the negative constant and the rest of the product.
        let public (|Negative|_|) (sp: SumPow) =
            match sp with //match Simplification.simplify sp with
            | PureConstantExpressionInteger n when n < 0 -> Some (Const (fromBigInt (abs n)), Const One)
            | PureConstantExpressionFloat n when n < 0. -> Some (Const (fromDouble (abs n)), Const One)
            | Prod xs ->
                match List.partition Misc.isPureConstInteger (List.map power xs) with
                | [], _ -> None
                | ts, fs ->
                    match List.reduce (Simplification.simpPureConst >> ( * )) ts with
                    | Const (CBigInteger n) when n < 0 -> Some (Const (fromBigInt (abs n)), List.reduce ( * ) fs)
                    | _ -> None
            | _ -> None

        // -- Standard name for named constants -- //

        let public Pi = Name "Pi"
        let public E = Name "E"
        let public I = Name "i"

        /// Equivalent to `Name "Pi"` for the π constant.
        let public (|Pi|_|) =
            function
            | Name "Pi" | Name "π" -> Some ()
            | _ -> None

        /// Equivalent to `Name "E"` for the e constant.
        let public (|E|_|) =
            function
            | Name "E" -> Some ()
            | _ -> None

        /// Equivalent to `Name "i"` for the imaginary unit.
        let public (|I|_|) =
            function
            | Name "i" -> Some ()
            | _ -> None

    /// The module containing SumPow's elementary arithmetic operations.
    module public ElementaryOperations =
        open PureConstantExpression

        /// A pseudo-function symbol (in the sense of elementary functions) that represents division by zero.
        let public divByZero (numerator: SumPow) =
            Fun ("DivByZero", [ numerator ])

        let public addition =
            function
            | Const x, Const y -> Const(x + y)

            | Const n, b when isZero n -> b
            | a, Const n when isZero n -> a

            | Frac(n, d), Frac(n', d') -> (n * d' + n' * d) / (d * d')

            | Sum [ t1 ], Sum ys -> Sum (t1 :: ys)
            | Sum xs, Sum [ t2 ] -> Sum (t2 :: xs)
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
            | Const(CBigInteger a), Const(CBigInteger b) ->
                let fixSign p q = if sign q > 0 then (p, q) else (-p, -q)
                let g = bigintGCD a b

                // Note: Since Constant is currently implemented via `double`, the value/precision of a `bigint`
                // can potentially be lost when converting to `double`.

                match fixSign (a / g) (b / g) with
                | a, b when b = 1I -> Const(fromBigInt a)
                | a, b when a = 1I -> Sum [ Term [ negPowId (Const(fromBigInt b)) ] ]
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

        //
        // We need `IComparable` for SumPow because we are using the `Map<'Key, 'Value>` type from standard F# library
        // which requires comparison; however comparison with SumPow is ill-defined. We can't tell how an expression is
        // greater than another, or lesser, etc. All we can say, more or less, is whether they are "sufficiently" equal.
        //
        // We have two choices:
        //  1. Change data structure when we need a dictionary-like data type ;
        //  2. Use a "weak" and "arbitrary" comparison that depends on the hashcode.
        //
        // We implement solution 2 for the following reasons: we want to retain the functional style of F# and the really
        // practical aspects of immutable (but persistent) data structures, like `Map`. By "weak" and "arbitrary" we don't
        // mean a buggy solution, but one in which the value of a comparison can change between runtimes (since the hash
        // is never the same from one runtime to the next in .NET) or is not interpretable as "greater" or "smaller" (for
        // example: is `Name "a"` greater or smaller than `Const 8`? It doesn't make much sense). As a result the notion of
        // being "greater" or "smaller" would be meaningless, but that doesn't matter because all we want is to respect
        // the comparison's properties of transitivity and symmetry (which the solution 2actually does!).
        //

        let inline public compareSumPow (sp1: SumPow) (sp2: SumPow) =
            compare (hash sp1) (hash sp2)

        let inline public compareTerm (t1: Term) (t2: Term) =
            compare (hash t1) (hash t2)

        let inline public comparePow (p1: Pow) (p2: Pow) =
            compare (hash p1) (hash p2)

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
                | Const a, Const b -> approximatelyEquals a b ValueNone
                | Sum xs, Sum ys -> Hashing.hashSum xs = Hashing.hashSum ys
                | Fun(a, xs), Fun(b, ys) -> a = b && xs = ys
                | _ -> false
            | _ -> false

    /// The module that transforms a SumPow expression into a MathRender.
    module private MathRenderSumPow =
        open ElementaryOperations
        open InternalFunction
        open MathRender

        [<Struct>]
        type private Sign =
            | Plus
            | Minus

            override this.ToString() =
                match this with
                | Plus -> "+"
                | Minus -> "-"

        let rec public toMathRender =
            function
            | Const (Constant c) -> MathRenderHelper.number c
            | Pi -> MathRenderHelper.symbol "π"
            | Name name -> (if String.length name > 1 then MathRenderHelper.simpleText else MathRenderHelper.symbol) name
            | Fun("Complex", [ re; im ]) -> toMRenderComplex re im
            | InternalFunction ifun -> toMRenderInternalFun ifun
            | Fun(fname, arguments) -> toMRenderFun fname arguments
            | Pattern.Frac(num, den) -> toMRenderFrac num den
            | Power(b, p) -> toMRenderPower b p
            | Prod prod -> toMRenderProd prod
            | SimplifiedSum.SumList sl -> toMRenderSum sl
            | other -> raise (UnknownSumPowExpressionException other)

        and private mayParens =
            function
            | Pattern.Frac(num, Const (Constant 1.)) -> toMathRender num
            | Pattern.Frac(num, den) -> MathRenderHelper.parens (toMRenderFrac num den)
            | Power(b', Const (Constant 1.)) -> toMathRender b'
            | Power (b', p') -> MathRenderHelper.parens (toMRenderPower b' p')
            | SimplifiedSum.SumList1 sl -> MathRenderHelper.parens (toMRenderSum sl)
            | other -> toMathRender other

        and private toMRenderComplex (re: SumPow) (im: SumPow) =
            toMathRender (re + Name "i" * im)

        and private toMRenderPower (b: SumPow) (p: SumPow) =
            match b, p with
            | b, Const (Constant 1.) -> toMathRender b
            | b, Const (Constant -1.) -> MathRenderHelper.frac (MathRenderHelper.number 1) (toMathRender b)
            | b, Pattern.Frac (num, den) -> toMRenderInternalFun (LiyhRoot (power (b, num), Some den))
            | b, p -> MathRenderHelper.power (mayParens b) (mayParens p)

        and private toMRenderFrac (num: SumPow) (den: SumPow) =
            match num, den with
            | num, Const (Constant 1.) -> toMathRender num
            | num, den -> MathRenderHelper.frac (toMathRender num) (toMathRender den)

        and private toMRenderProd (prod: (SumPow * SumPow) list) =

            let rec loop result lst =
                let catResult cd addon =
                    if List.isEmpty result then [ addon ]
                    else
                        (MathRenderHelper.group result
                         :: if cd then MathRenderHelper.cdot else MathRenderHelper.nothing
                         :: addon
                         :: [])

                match lst with
                | [] -> result
                | (b, p) :: lst ->
                    let cat =
                        match b with
                        | Const _ | Name _ | Fun _ | Pattern.Frac _ | Power _ -> false
                        | _ -> true

                    let expr =
                        match p with
                        | Const (Constant 1.) -> mayParens b
                        | _ -> toMRenderPower b p

                    loop (catResult cat expr) lst

            match Misc.prodToSumPow prod with
            | ProdWithKeep Misc.isPureConstInteger (cst, rest, _) ->
                let cst = List.filter (function Const (Constant 1.) -> false | _ -> true) cst
                let rest = List.filter (function (Const (Constant 1.), Const (Constant 1.)) -> false | _ -> true) rest

                let latexConstant =
                    match cst with
                    | [] -> MathRenderHelper.nothing
                    | c :: cst -> List.fold (fun acc r -> acc ++ MathRenderHelper.cdot ++ toMathRender r) (toMathRender c) cst

                let latexRest = MathRenderHelper.group (loop [] rest)

                if List.isEmpty cst then MathRenderHelper.group (loop [] rest)
                elif List.length cst > 1 then
                    if List.length rest > 1 then MathRenderHelper.parens latexConstant ++ MathRenderHelper.parens latexRest
                    elif List.length rest = 1 then MathRenderHelper.parens latexConstant ++ MathRenderHelper.cdot ++ latexRest
                    else latexConstant
                else
                    match cst with
                    | [ Const (Constant -1.) ] -> MathRenderHelper.minus ++ latexRest
                    | _ -> latexConstant ++ latexRest

            | Prod prod -> MathRenderHelper.group (loop [] prod)
            | other -> raise (UnknownSumPowExpressionException other)

        and private toMRenderSum (sl: SumPow list) =

            let rec loop result (lst: SumPow list) =
                let catResult sign addon =
                    if List.isEmpty result then if sign = Plus then [ addon ] else [ MathRenderHelper.minus ++ addon ]
                    else MathRenderHelper.group result :: MathRenderHelper.symbol (string sign) :: addon :: []

                match lst with
                | [] -> result
                | Const (Constant 0.) :: lst -> loop result lst
                | Const (Constant n) :: lst when n < 0 -> loop (catResult Minus (MathRenderHelper.number (abs n))) lst
                | Negative (Const (Constant 1.), y) :: lst -> loop (catResult Minus (toMathRender y)) lst
                | Negative (Const (Constant n), y) :: lst -> loop (catResult Minus (MathRenderHelper.number n ++ MathRenderHelper.group [ toMathRender y ])) lst
                | Negative (x, y) :: lst -> loop (catResult Minus (toMathRender x ++ MathRenderHelper.cdot ++ MathRenderHelper.group [ toMathRender y ])) lst
                | x :: lst -> loop (catResult Plus (toMathRender x)) lst

            MathRenderHelper.group (loop [] sl)

        and private toMRenderInternalFun =
            function
            | LiyhPow(b, p) -> toMRenderPower b p
            | LiyhRoot(x, Some (Const (Constant 2.)))
            | LiyhRoot(x, None) -> MathRenderHelper.sqrt (toMathRender x)
            | LiyhRoot(x, Some b) -> MathRenderHelper.root (toMathRender x) (toMathRender b)
            | LiyhLog(x, None) -> MathRenderHelper.ln (toMathRender x)
            | LiyhLog(x, Some E) -> MathRenderHelper.ln (toMathRender x)
            | LiyhLog(x, Some b) -> MathRenderHelper.log (toMathRender x) (toMathRender b)
            | LiyhExp x -> MathRenderHelper.power (MathRenderHelper.symbol "e") (toMathRender x)
            | LiyhSin x -> MathRenderHelper.func "sin" [ toMathRender x ]
            | LiyhCos x -> MathRenderHelper.func "cos" [ toMathRender x ]
            | LiyhTan x -> MathRenderHelper.func "tan" [ toMathRender x ]
            | LiyhCsc x -> MathRenderHelper.func "csc" [ toMathRender x ]
            | LiyhSec x -> MathRenderHelper.func "sec" [ toMathRender x ]
            | LiyhCot x -> MathRenderHelper.func "cot" [ toMathRender x ]
            | LiyhArSin x -> MathRenderHelper.func "arcsin" [ toMathRender x ]
            | LiyhArCos x -> MathRenderHelper.func "arccos" [ toMathRender x ]
            | LiyhArTan x -> MathRenderHelper.func "arctan" [ toMathRender x ]
            | LiyhArCsc x -> MathRenderHelper.func "arcsc" [ toMathRender x ]
            | LiyhArSec x -> MathRenderHelper.func "arsec" [ toMathRender x ]
            | LiyhArCot x -> MathRenderHelper.func "arcot" [ toMathRender x ]
            | LiyhSinh x -> MathRenderHelper.func "sinh" [ toMathRender x ]
            | LiyhCosh x -> MathRenderHelper.func "cosh" [ toMathRender x ]
            | LiyhTanh x -> MathRenderHelper.func "tanh" [ toMathRender x ]
            | LiyhCsch x -> MathRenderHelper.func "csch" [ toMathRender x ]
            | LiyhSech x -> MathRenderHelper.func "sech" [ toMathRender x ]
            | LiyhCoth x -> MathRenderHelper.func "coth" [ toMathRender x ]
            | LiyhArSinh x -> MathRenderHelper.func "arsinh" [ toMathRender x ]
            | LiyhArCosh x -> MathRenderHelper.func "arcosh" [ toMathRender x ]
            | LiyhArTanh x -> MathRenderHelper.func "artanh" [ toMathRender x ]
            | LiyhArCsch x -> MathRenderHelper.func "arcsch" [ toMathRender x ]
            | LiyhArSech x -> MathRenderHelper.func "arsech" [ toMathRender x ]
            | LiyhArCoth x -> MathRenderHelper.func "arcoth" [ toMathRender x ]
            | LiyhSinc x -> MathRenderHelper.func "sinc" [ toMathRender x ]
            | LiyhAbs x -> MathRenderHelper.abs (toMathRender x)
            | LiyhSgn x -> MathRenderHelper.func "sgn" [ toMathRender x ]
            | LiyhDelta x -> MathRenderHelper.symbol "δ" ++ MathRenderHelper.subscript (MathRenderHelper.simpleText "Dirac") ++ MathRenderHelper.parens (MathRenderHelper.group [ toMathRender x ])
            | LiyhCeil x ->  MathRenderHelper.func "ceil" [ toMathRender x ]
            | LiyhFloor x -> MathRenderHelper.func "floor" [ toMathRender x ]
            | LiyhRound x -> MathRenderHelper.func "round" [ toMathRender x ]
            | LiyhId x -> toMathRender x

        and private toMRenderFun (fname: string) (arguments: SumPow list) =
            MathRenderHelper.func fname (List.map toMathRender arguments)

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
                    { atom = Atomic.Identifier "Prod"
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
        override this.ToString() = "<SumPow>" //Latex.toLatex this

        // -- Implement interfaces -- //

        interface IComparable with
            member sp1.CompareTo obj =
                match obj with
                | :? SumPow as sp2 -> Comparison.compareSumPow sp1 sp2
                | _ -> invalidArg "obj" "cannot compare value of different types"

        interface ISymbolic with
            member this.ToSymbolic() = toSymbolic this
            member this.ToMathRender() = Some(MathRenderSumPow.toMathRender this)
            member this.ToMathRenderOrString() = Choice1Of2 (MathRenderSumPow.toMathRender this)

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

    /// Checks whether the two given expressions are equal or not using a random value generation heuristic.
    /// This method is good for disproving equality, but is not safe for proving equality. This method of checking
    /// equality has the advantage of not using canonical transformations and is therefore fast.
    let inline public ( == ) (sp1: SumPow) (sp2: SumPow) =
        EqualityTest.equalityTest sp1 sp2

    /// A "Term" is a product of powers.
    [<CustomEquality; CustomComparison>]
    type public Term =
        /// A `Term` is a product of powers.
        | Term of Pow list

        override this.GetHashCode() = Hashing.hashTerm this
        override this.Equals arg = Equality.equalsTerm this arg

        interface IComparable with
            member term1.CompareTo obj =
                match obj with
                | :? Term as term2 -> Comparison.compareTerm term1 term2
                | _ -> invalidArg "obj" "cannot compare value of different types"

    /// A "Pow" is a SumPow tuple.
    [<CustomEquality; CustomComparison>]
    type public Pow =
        /// A `Pow` is a SumPow tuple.
        | Pow of SumPow * SumPow

        override this.GetHashCode() = Hashing.hashPow this
        override this.Equals arg = Equality.equalsPow this arg

        interface IComparable with
            member pow1.CompareTo obj =
                match obj with
                | :? Pow as pow2 -> Comparison.comparePow pow1 pow2
                | _ -> invalidArg "obj" "cannot compare value of different types"

    /// This module contains some utilities that make it easier to manipulate SumPow's sums.
    module public SimplifiedSum =
        open ElementaryOperations

        exception public NotASimplifiedSum of SumPow

        /// Converts the given list of SumPow into a sum.
        let inline public fromList (sl: SumPow list) =
            // It's quicker than doing `List.reduce ( + ) sl`.
            match sl with
            | [] -> Const Zero
            | sl -> Sum (List.map termId sl)

        /// In SumPow, a sum is a list of products of powers, represented more elegantly by single constructors `Term` and `Pow`.
        /// These last two types are abstractions which it's sometimes useful to dispense with for simplicity's sake, so a
        /// "simplified sum" represents SumPow's sum as the following type without `Term` nor `Pow` constructors.
        type public SimplifiedSum = (SumPow * SumPow) list list

        /// Convert the given `SumPow` sum (list of terms) to `SimplifiedSum`.
        let inline public simplifiedSum (sum: Term list) : SimplifiedSum =
            //[ for Term term in sum -> [ for Pow(b, p) in term -> (b, p) ] ]

            [ for Term term in sum do
                // I'm not a fan of this, it's like hiding a problem under the carpet (it means that a calculation
                // has generated an empty list for a sum or product, which can't normally be valid).
                if not (List.isEmpty term) then [ for Pow(b, p) in term -> (b, p) ] ]

        /// Convert the given `SumPow` sum to `SimplifiedSum`.
        let inline public simplifiedSum' (expr: SumPow) : SimplifiedSum =
            match expr with
            | Sum terms -> simplifiedSum terms
            | other -> raise (NotASimplifiedSum other)

        /// Convert the given `SimplifiedSum` to `SumPow`.
        let public simplifiedSumToSum (ss: SimplifiedSum) =
            let inline makeTerm term = [ for (b, p) in term -> power'(b, p) ]
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
        let public mapPowFlatten (mapping: SumPow * SumPow -> 't) (ss: SimplifiedSum) =
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

        /// Converts the sum into a product list (the inner list is a product and the outer list a the sum).
        let public sumAsProdList =
            function
            | Sum sum -> List.map (function Term t -> List.map (function Pow(b, p) -> power (b, p)) t) sum
            | other -> [ [ other ] ]

        /// An active pattern that converts the sum into a SumPow list. Requires more than one element in the sum.
        let public (|SumList1|_|) (sp: SumPow) =
            Option.ofBool (sumAsSumPowList sp) (fun xs -> List.length xs > 1)

        /// An active pattern that converts the sum into a SumPow list. Requires at least one element in the sum.
        let public (|SumList|_|) (sp: SumPow) =
            Option.ofBool (sumAsSumPowList sp) (fun xs -> List.length xs > 0)

    /// A "pure constant expression" is an expression containing no variables or parameters, just numbers. For simplicity,
    /// even constants such as pi and e are not considered (for now). This module provides utilities for simplifying and
    /// working with constant expressions or matching them.
    /// 
    /// The simplifier (hopefully) handles integers, rationals, powers, fractions, roots, sums and products.
    module public PureConstantExpression =
        open SimplifiedSum
        open ElementaryOperations
        open InternalFunction

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
            | SimpIntRoot.IrredRoot(x, nth) -> liyhRoot (Const x, Const nth)
            | SimpIntRoot.IntRootProd (c, (x, nth)) -> c * liyhRoot (Const x, Const nth)

        /// Checks if the given expression is a "pure constant" (i.e. an expression containing no `Name string` data).
        /// The returned expression is unvalued.
        [<MethodImpl(MethodImplOptions.AggressiveOptimization)>]
        let rec public (|PureConstantExpression|_|) =

            let matcher =
                function
                | (E | I | Pi) as sp -> Some sp // Known named constants
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

            // Many similar calls should be made to this active-pattern, in the interests of general
            // performance we can memoize the result.
            memoize matcher

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

            let matcher =
                function
                | Const _ as cst -> cst
                | Power(b, One) -> csimplify b
                | Power(Root(x, PureConstantExpressionInteger nth), PureConstantExpressionInteger p) as pc ->
                    if p = nth then csimplify x
                    elif p % nth = 0 then csimplify (x ** (p / nth))
                    else pc

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
                | InternalFunction ifun -> simplifyFunction ifun
                | Fun(fname, args) -> Fun(fname, List.map csimplify args)
                | other -> other

            // Many similar calls should be made to this active-pattern, in the interests of general
            // performance we can memoize the result.
            memoize matcher

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
                    (iacc, facc, oacc * csimplify (b ** p))

                // | b, p ->
                //     (iacc, facc, oacc * power (b, p))

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
        open PureConstantExpression
        open InternalFunction
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
            if not (isPureConstantExpression sp) then
                raise (ExpressionIsNotPureConstantException sp)

            csimplify sp

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
            | num, den -> num / den

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
                    | PureConstantExpression c, [] -> makeSimp result (constant + c) xs

                    | factor, term ->
                        match Map.tryFind term result with
                        | None ->
                            match factor with
                            | Zero -> makeSimp result constant xs
                            | factor -> makeSimp (Map.add term factor result) constant xs
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

            //FixedPoint.tryFixedPoint 5 //>> memoize
            FixedPoint.fixedPointMax' 5 >> memoize
            <| function
                | PureConstantExpression cst -> simpPureConst cst
                | Name _ as name -> name

                | Power (b, One) -> simplify b
                | Power (_, Zero) -> Const One
                | Frac (num, den) -> simpFrac num den

                | Sum xs -> simpSum xs

                | InternalFunction ifun -> simplifyFunction ifun
                | Fun(name, args) -> Fun(name, List.map simplify args)
                | other -> other

        /// Simplify the given expression after developing it to the maximum possible extent.
        let public expandAndSimplify =
            Expand.fullExpand >> Simplification.simplify

        /// Expand the given expression to the maximum possible extent after simplifying it.
        let public simplifyAndExpand =
            Simplification.simplify >> Expand.fullExpand

        /// Simplify and expand until a fixed point.
        let public fixSimplify =
            FixedPoint.fixedPointMax' 10 Simplification.simplifyAndExpand

    /// Development (distributivity of sum and product) of SumPow algebraic expressions.
    [<RequireQualifiedAccess>]
    module public Expand =
        open PureConstantExpression
        open ElementaryOperations
        open SimplifiedSum

        /// Implements Newton's binomial for `(x + y)^n`. Takes the two sum terms and the integer exponent and returns
        /// the resulting sum. See https://en.wikipedia.org/wiki/Binomial_theorem.
        let private newtonBinomial (x: Pow list) (y: Pow list) (n: int) =

            let binomialTerm (k: int) =
                let spk = Const k
                let spnk = Const(double (n - k))
                let bin = Const(binomial n k)

                let inline mapping (m: SumPow) (Pow(b, p)) =
                    power' (expand b, expand p * m)

                let xTerm = List.map (mapping spk) x
                let yTerm = List.map (mapping spnk) y

                powId bin
                :: (xTerm @ yTerm)
                |> Simplification.basicTermSimp
                |> Flatten.flattenTerm
                |> Term

            Sum [ for k = 0 to n do binomialTerm k ]

        /// Implements the generalized binomial theorem for `(x₁ + x₂ + ⋅⋅⋅ + xₘ)^n`.
        /// See https://en.wikipedia.org/wiki/Multinomial_theorem.
        let private newtonMultinomial (terms: Term list) (n: int) =
            let len = List.length terms

            /// Generates the list of powers that will be involved in the final sum.
            let rec inner start currentSum currentCombination combinations =
                if List.length currentCombination = len then
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
                let folder acc p term = acc * power (sumId term, Const (int p))
                List.fold2 folder mul vec terms

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

        /// Expand a sum or a product power.
        let private expandPow =
            function
            | Prod xs, p -> Sum [ Term(List.map (fun (b, p') -> power'(expand b, expand p' * p)) xs) ], Const One

            | Sum terms, PureConstantExpressionInteger p when p > 0 ->

                // Null terms are filtered out.
                match List.filter (sumId >> ( == ) (Const Zero) >> not) terms with
                | [ term ] -> sumId term, Const p
                | [ Term x; Term y ] -> newtonBinomial x y p, Const One
                | terms -> newtonMultinomial terms p, Const One

            | b, p -> expand b, expand p

        /// Expand a product.
        let private expandTerm (term: (SumPow * SumPow) list) =
            let (x :: xs) = List.map expandPow term
            List.fold (fun acc (b, p) -> distribute (acc, (b ** p))) (power x) xs

        /// Expands the given expression.
        let public expand =

            let inner =
                function
                | SimpleSP x -> x
                | Power(b, p) -> power (expandPow (b, p))
                | Prod prod -> expandTerm prod
                | SimplifiedSum ss -> Sum (manyTermId (List.map expandTerm ss))
                | other -> other

            memoize inner

        /// Apply expansion until a fixed point. Might throw an exception if a fixed point is not found.
        let public fullExpand = FixedPoint.tryFixedPoint 20 expand

    /// A module for making substitutions in SumPow.
    module public Subst =
        open ElementaryOperations
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
        let public manySubstVar (pairs: IDictionary<string, SumPow>) (expr: SumPow) =

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

        /// Replaces the variables (many `Name string`) with the associated constant.
        let public manySubstVarConst (pairs: IDictionary<string, Constant>) =
            manySubstVar (dict (Seq.map (function KeyValue(k, v) -> (k, Const v)) pairs))

        /// Replaces the variables (many `Name string`) with the associated constant.
        let public manySubstVarDouble (pairs: IDictionary<string, double>) =
            manySubstVar (dict (Seq.map (function KeyValue(k, v) -> (k, Const (Constant v))) pairs))

        (* Helpers for the `hsubst` substitution function. *)

        /// Checks whether every item in `sublist` is contained in `mainlist`, regardless of the positions of the items.
        /// If yes, then returns the list of positions.
        let inline private findPositions sublist mainlist =

            let rec loop sub main acc =
                match sub with
                | [] -> Some acc
                | s :: ss ->
                    match List.tryFindIndex (( == ) s) main with
                    | None -> None
                    | Some idx -> loop ss main (idx :: acc)

            loop sublist mainlist []

        /// Removes all elements from `lst` which are at positions given by `positions`.
        let inline private removeAtPositions positions lst =
            let positionsSet = Set.ofList positions

            List.mapi tuple2 lst
            |> List.filter (fun (i, _) -> not (Set.contains i positionsSet))
            |> List.map snd

        /// Combines functions `findPositions` and `removeAtPositions`.
        let inline private findAndRemoveSublist sublist mainlist =
            Option.map (flip removeAtPositions mainlist) (findPositions sublist mainlist)

        /// Substitutes (mainly syntactically) the expression `toSub` with `sub` in the given expression.
        ///
        /// This function is limited by the fact that it cannot guess that an equivalent but too different
        /// sub-expression is considered valid for replacement, but it works if the sub-expression is entirely
        /// present (taking commutativity into account) and/or with the comparison according to `EqualityTest`.
        ///
        /// The more complex the expression to be substituted, the slower it will take to execute.
        [<MethodImpl(MethodImplOptions.AggressiveOptimization)>]
        let public hsubst (toSub: SumPow) (sub: SumPow) (expr: SumPow) =

            // If it is a matter of substituting a simple variable, then execution is redirected
            // to the way more efficient `substVar` function.

            match toSub with
            | Name name -> substVar name sub expr
            | toSub ->

                // We consider two main patterns which are both subject to commutativity: the sum and the product.
                // In addition, we consider the type of sub-expression to be searched for. If the sub-expression to
                // be searched for is also a sum or a product, then more complex mechanisms enter the process.

                let rec hsubst =
                    function
                    | sp when (sp = toSub || sp == toSub) -> sub // `=` is faster but less general than `==`.
                    | Fun(fname, args) -> Fun(fname, List.map hsubst args)

                    | Prod xs ->
                        let xs' = List.map power xs

                        /// When no or `None` match occurs.
                        let inline default' () =
                            Misc.prodToSumPow (List.map (fun (b, p) -> hsubst b, hsubst p) xs)

                        match toSub with

                        // The expression is a product and the sub-expression to be searched for is a product.
                        | Prod ys ->
                            let ys' = List.map power ys

                            match findAndRemoveSublist ys' xs' with
                            | None -> default' ()
                            | Some unsub -> sub * hsubst (List.reduce ( * ) unsub)

                        // The expression is a product and the sub-expression to be searched for is a sum.
                        | Sum ys ->
                            let ys' = sumAsSumPowList (Sum ys)

                            match findAndRemoveSublist ys' xs' with
                            | None -> default' ()
                            | Some unsub -> sub + hsubst (Sum(manyTermId unsub))

                        | _ -> default' ()

                    | Sum xs ->
                        match toSub with

                        // The expression is a sum and the sub-expression to be searched for is a product.
                        | Prod ys ->
                            let sapl = sumAsProdList (Sum xs)
                            let ys' = List.map power ys

                            let inline mapper xs' =
                                match findAndRemoveSublist ys' xs' with
                                | None -> hsubst (List.reduce ( * ) xs')
                                | Some unsub -> sub * hsubst (List.reduce ( * ) unsub)

                            Sum (manyTermId (List.map mapper sapl))

                        // The expression is a sum and the sub-expression to be searched for is a sum.
                        | Sum ys ->

                            let xs' = sumAsSumPowList (Sum xs)
                            let ys' = sumAsSumPowList (Sum ys)

                            match findAndRemoveSublist ys' xs' with
                            | None -> Sum(mapPow' (fun b p -> Pow(hsubst b, hsubst p)) xs)
                            | Some unsub -> sub + hsubst (Sum(manyTermId unsub))

                        | _ -> Sum(mapPow' (fun b p -> Pow(hsubst b, hsubst p)) xs)

                    | other -> other

                hsubst expr

        (* Helpers for the `suggest` substitution function. *)

        /// Generates all list combinations of lengths > 1 from the given list. For example,
        /// 
        ///     combination [ 'a'; 'b'; 'c' ] ≡ [ [ 'a'; 'b'; 'c' ]; [ 'a'; 'b' ]; [ 'a'; 'c' ]; [ 'b'; 'c' ] ]
        /// 
        /// This code explodes very quickly (it actually follows the sequence of Eulerian numbers), and in our case we'll
        /// restrict the input to 10 elements in the list for our purpose.
        let private combination (lst: 't list) =

            let rec inner result =
                function
                | [] -> result
                | x :: xs ->
                    let newItem = List.map (fun c -> x :: c) result
                    inner (result @ newItem) xs

            // If `lst` has 10 items then the result will have 2036 ones, for example, and with 11 items the
            // result will have 4083 ones! To avoid performance loss, we limit the size of the input.

            let lst = List.distinct lst

            if List.length lst <= 10 then inner [[]] lst |> List.filter (fun lst -> List.length lst > 1) |> Some
            else None

        let inline private addOrUpdate k r =
            Map.addOrUpdate k 1 r (( + ) 1)

        /// Suggest sub-expressions of a sum, taking commutativity into account.
        let private mayAppendSum (sl: SumPow list) (result: Map<SumPow, int>) =
            match combination sl |> Option.map (List.map (manyTermId >> Sum)) with
            | None | Some [] -> result
            | Some lst -> List.fold (flip addOrUpdate) result lst

        /// Converts a SumPow list into a product with each factor to the power of 1.
        let private spListTo1Prod (pd: SumPow list) =
            List.map (fun p -> power' (p, Const One)) pd |> Term |> sumId

        /// Suggest sub-expressions of a product, taking commutativity into account.
        let private mayAppendProd (prod: (SumPow * SumPow) list) (result: Map<SumPow, int>) =
            let gp = List.groupBy snd prod |> List.map (snd >> List.map fst)

            let inline folder (result: Map<SumPow, int>) (pd: SumPow list) =
                match combination pd |> Option.map (List.map spListTo1Prod) with
                | None | Some [] -> result
                | Some lst -> List.fold (flip addOrUpdate) result lst

            List.fold folder result gp

        /// Returns an array of suggested sub-expressions to be substituted. Suggested sub-expressions are those that
        /// will appear in the global expression a number of times greater than the given `criterion` (default is `>1`).
        /// Suggested sub-expressions are sorted by number of occurrences.
        /// This function will be useful for operations requiring non-user-assisted substitution.
        let public suggest (sp: SumPow) (criterion: int option) =
            let criterion = Option.defaultValue 1 criterion

            if criterion < 0 then
                invalidArg "criterion" "The suggestion criterion cannot be negative."

            let rec inner result (sp: SumPow) =
                match sp with
                | Const _ | Name _ -> result // not interesting to substitute

                | Prod prod ->
                    let result = mayAppendProd prod result
                    List.fold (fun acc (b, p) -> inner (inner acc b) p) result prod

                | SumList1 sl ->
                    let result = mayAppendSum sl result
                    List.fold inner result sl

                | Fun(_, args) ->
                    let result = addOrUpdate sp result
                    List.fold inner result args

                | other -> addOrUpdate other result

            inner Map.empty sp
            |> Map.toArray
            |> Array.filter (fun (_, k) -> k > criterion)
            |> Array.sortByDescending snd
            |> Array.map fst

    /// A module for finding elements in SumPow (sub-)expressions.
    module public Find =
        open SimplifiedSum

        //
        // Checking whether a sub-expression is contained in an expression is an undecidable problem (like equality),
        // but it is still applicable in a wide range of cases. The element determining the success or failure of such 
        // search is (delegated to) the quality of the given predicate and/or the use of EqualityTest heuristic.
        //

        /// Given a predicate, returns a list of all sub-expressions of the given expression that satisfy it. If no
        /// element has satisfied the predicate, then returns `None`. The `tryFind` function is limited by the
        /// complexity of the predicate, as is the management of the commutativity of the sum and product.
        let public tryFind (predicate: SumPow -> bool) (source: SumPow) =

            let rec loop (sp: SumPow) =
                let inline hpow (Pow (b, p)) = loop b @ loop p

                if predicate sp then [ sp ] else []
                @ match sp with
                  | Name _ | Const _ -> [] // No sub-expression to be checked.
                  | Sum [ Term term ] -> List.collect hpow term
                  | (SumList1 lst | Fun (_, lst)) -> List.collect loop lst

            Option.ofBool (loop source) (not << List.isEmpty)

        /// Given a predicate, returns whether or not the given expression contains at least one sub-expression
        /// satisfying it. The `containsBy` function is limited by the complexity of the predicate, as is the management
        /// of the commutativity of the sum and product.
        let public containsBy (predicate: SumPow -> bool) (source: SumPow) =

            let rec loop =
                function
                | sp when predicate sp -> true
                | Sum sum ->
                    let inline hpow (Pow (b, p)) = loop b || loop p
                    let inline hterm (Term term) = List.containsBy hpow term
                    List.containsBy hterm sum
                | Fun(_, args) -> List.containsBy loop args
                | _ -> false

            loop source

        /// Checks with syntax equality whether the given expression contains the specified sub-expression.
        let inline public contains (value: SumPow) =
            containsBy (( = ) value)

        /// Uses the EqualityTest heuristic to check whether the given expression contains the specified sub-expression.
        let inline public containsStronger (value: SumPow) =
            containsBy (( == ) value)

        /// An active pattern that match a given predicate.
        let public (|When|_|) (predicate: SumPow -> bool) =
            tryFind (memoize predicate)

    /// A module that implements the evaluation of elementary functions.
    module public InternalFunction =
        open PureConstantExpression

        /// List of elementary functions handled by Liyh.
        let public ifuns =
            [|"Pow"; "Root"; "Sqrt"; "Log"; "Exp"; "Sin"; "Cos"; "Tan"; "Csc"; "Sec"; "Cot"; "Sgn"; "Delta"; "Id"
              "ArSin"; "ArCos"; "ArTan"; "ArCsc"; "ArSec"; "ArCot"; "Sinh"; "Cosh"; "Tanh"; "Csch"; "Ceil"; "Round"
              "Sech"; "Coth"; "ArSinh"; "ArCosh"; "ArTanh"; "ArCsch"; "ArSech"; "ArCoth"; "Sinc"; "Abs"; "Floor" |]

        /// List the various built-in elementary functions in Liyh.
        type public InternalFunction =
            | LiyhPow of base': SumPow * exp: SumPow
            | LiyhRoot of base': SumPow * exp: SumPow option // default: Sqrt
            | LiyhLog of arg: SumPow * base': SumPow option // default: Ln
            | LiyhExp of arg: SumPow
            | LiyhSin of arg: SumPow
            | LiyhCos of arg: SumPow
            | LiyhTan of arg: SumPow
            | LiyhCsc of arg: SumPow
            | LiyhSec of arg: SumPow
            | LiyhCot of arg: SumPow
            | LiyhArSin of arg: SumPow
            | LiyhArCos of arg: SumPow
            | LiyhArTan of arg: SumPow
            | LiyhArCsc of arg: SumPow
            | LiyhArSec of arg: SumPow
            | LiyhArCot of arg: SumPow
            | LiyhSinh of arg: SumPow
            | LiyhCosh of arg: SumPow
            | LiyhTanh of arg: SumPow
            | LiyhCsch of arg: SumPow
            | LiyhSech of arg: SumPow
            | LiyhCoth of arg: SumPow
            | LiyhArSinh of arg: SumPow
            | LiyhArCosh of arg: SumPow
            | LiyhArTanh of arg: SumPow
            | LiyhArCsch of arg: SumPow
            | LiyhArSech of arg: SumPow
            | LiyhArCoth of arg: SumPow
            | LiyhSinc of arg: SumPow
            | LiyhAbs of arg: SumPow
            | LiyhSgn of arg: SumPow
            | LiyhDelta of arg: SumPow  // dirac-delta (not a true function but useful)
            | LiyhCeil of arg: SumPow
            | LiyhFloor of arg: SumPow
            | LiyhRound of arg: SumPow
            | LiyhId of arg: SumPow

        /// Pattern-match an elementary built-in function.
        let public (|InternalFunction|_|) =
            function
            | Fun(fname, _) when not (Array.contains fname ifuns) -> None

            | Power(base', exp)
            | Fun("Pow", [ base'; exp ]) -> Some(InternalFunction.LiyhPow(base', exp))
            | Fun("Root", [ base'; exp ]) -> Some(InternalFunction.LiyhRoot(base', Some exp))
            | Fun("Sqrt", [ arg ]) -> Some(InternalFunction.LiyhRoot(arg, None))
            | Fun("Log", [ arg; base' ]) -> Some(InternalFunction.LiyhLog(arg, Some base'))
            | Fun("Log", [ arg ]) -> Some(InternalFunction.LiyhLog(arg, None))
            | Fun("Exp", [ arg ]) -> Some(InternalFunction.LiyhExp arg)
            | Fun("Sin", [ arg ]) -> Some(InternalFunction.LiyhSin arg)
            | Fun("Cos", [ arg ]) -> Some(InternalFunction.LiyhCos arg)
            | Fun("Tan", [ arg ]) -> Some(InternalFunction.LiyhTan arg)
            | Fun("Csc", [ arg ]) -> Some(InternalFunction.LiyhCsc arg)
            | Fun("Sec", [ arg ]) -> Some(InternalFunction.LiyhSec arg)
            | Fun("Cot", [ arg ]) -> Some(InternalFunction.LiyhCot arg)
            | Fun("ArSin", [ arg ]) -> Some(InternalFunction.LiyhArSin arg)
            | Fun("ArCos", [ arg ]) -> Some(InternalFunction.LiyhArCos arg)
            | Fun("ArTan", [ arg ]) -> Some(InternalFunction.LiyhArTan arg)
            | Fun("ArCsc", [ arg ]) -> Some(InternalFunction.LiyhArCsc arg )
            | Fun("ArSec", [ arg ]) -> Some(InternalFunction.LiyhArSec arg )
            | Fun("ArCot", [ arg ]) -> Some(InternalFunction.LiyhArCot arg )
            | Fun("Sinh", [ arg ]) -> Some(InternalFunction.LiyhSinh arg)
            | Fun("Cosh", [ arg ]) -> Some(InternalFunction.LiyhCosh arg)
            | Fun("Tanh", [ arg ]) -> Some(InternalFunction.LiyhTanh arg)
            | Fun("Csch", [ arg ]) -> Some(InternalFunction.LiyhCsch arg)
            | Fun("Sech", [ arg ]) -> Some(InternalFunction.LiyhSech arg)
            | Fun("Coth", [ arg ]) -> Some(InternalFunction.LiyhCoth arg)
            | Fun("ArSinh", [ arg ]) -> Some(InternalFunction.LiyhArSinh arg)
            | Fun("ArCosh", [ arg ]) -> Some(InternalFunction.LiyhArCosh arg)
            | Fun("ArTanh", [ arg ]) -> Some(InternalFunction.LiyhArTanh arg)
            | Fun("ArCsch", [ arg ]) -> Some(InternalFunction.LiyhArCsch arg)
            | Fun("ArSech", [ arg ]) -> Some(InternalFunction.LiyhArSech arg)
            | Fun("ArCoth", [ arg ]) -> Some(InternalFunction.LiyhArCoth arg)
            | Fun("Sinc", [ arg ]) -> Some(InternalFunction.LiyhSinc arg)
            | Fun("Abs", [ arg ]) -> Some(InternalFunction.LiyhAbs arg)
            | Fun("Sgn", [ arg ]) -> Some(InternalFunction.LiyhSgn arg)
            | Fun("Delta", [ arg ]) -> Some(InternalFunction.LiyhDelta arg)
            | Fun("Ceil", [ arg ]) -> Some(InternalFunction.LiyhCeil arg)
            | Fun("Floor", [ arg ]) -> Some(InternalFunction.LiyhFloor arg)
            | Fun("Round", [ arg ]) -> Some(InternalFunction.LiyhRound arg)
            | Fun("Id", [ arg ]) -> Some(InternalFunction.LiyhId arg)

            | _ -> None

        [<AutoOpen>]
        module public σ =
            let public liyhPow (b, p) = Fun("Pow", [ b; p ])
            let public liyhRoot (x, nth) = Fun("Root", [ x; nth ])
            let public liyhSqrt x = Fun("Sqrt", [ x ])
            let public liyhLog (x, b) = Fun("Log", [ x; b ])
            let public liyhLn x = Fun("Log", [ x; Name "E" ])
            let public liyhExp x = Fun("Exp", [ x ])
            let public liyhSin x = Fun("Sin", [ x ])
            let public liyhCos x = Fun("Cos", [ x ])
            let public liyhTan x = Fun("Tan", [ x ])
            let public liyhCsc x = Fun("Csc", [ x ])
            let public liyhSec x = Fun("Sec", [ x ])
            let public liyhCot x = Fun("Cot", [ x ])
            let public liyhArSin x = Fun("ArSin", [ x ])
            let public liyhArCos x = Fun("ArCos", [ x ])
            let public liyhArTan x = Fun("ArTan", [ x ])
            let public liyhArCsc x = Fun("ArCsc", [ x ])
            let public liyhArSec x = Fun("ArSec", [ x ])
            let public liyhArCot x = Fun("ArCot", [ x ])
            let public liyhSinh x = Fun("Sinh", [ x ])
            let public liyhCosh x = Fun("Cosh", [ x ])
            let public liyhTanh x = Fun("Tanh", [ x ])
            let public liyhCsch x = Fun("Csch", [ x ])
            let public liyhSech x = Fun("Sech", [ x ])
            let public liyhCoth x = Fun("Coth", [ x ])
            let public liyhArSinh x = Fun("ArSinh", [ x ])
            let public liyhArCosh x = Fun("ArCosh", [ x ])
            let public liyhArTanh x = Fun("ArTanh", [ x ])
            let public liyhArCsch x = Fun("ArCsch", [ x ])
            let public liyhArSech x = Fun("ArSech", [ x ])
            let public liyhArCoth x = Fun("ArCoth", [ x ])
            let public liyhSinc x = Fun("Sinc", [ x ])
            let public liyhAbs x = Fun("Abs", [ x ])
            let public liyhSgn x = Fun("Sgn", [ x ])
            let public liyhDelta x = Fun("Delta", [ x ])
            let public liyhCeil x = Fun("Ceil", [ x ])
            let public liyhFloor x = Fun("Floor", [ x ])
            let public liyhRound x = Fun("Round", [ x ])
            let public liyhId x = Fun("Id", [ x ])

        /// Convert the InternalFunction representation to the SumPow representation.
        let public toSumPow =
            function
            | LiyhPow(b, p) -> liyhPow (b, p)
            | LiyhRoot(x, None) -> liyhSqrt x
            | LiyhRoot(x, Some nth) -> liyhRoot (x, nth)
            | LiyhLog(x, None) -> liyhLn x
            | LiyhLog(x, Some b) -> liyhLog (x, b)
            | LiyhExp x -> liyhExp x
            | LiyhSin x -> liyhSin x
            | LiyhCos x -> liyhCos x
            | LiyhTan x -> liyhTan x
            | LiyhCsc x -> liyhCsc x
            | LiyhSec x -> liyhSec x
            | LiyhCot x -> liyhCot x
            | LiyhArSin x -> liyhArSin x
            | LiyhArCos x -> liyhArCos x
            | LiyhArTan x -> liyhArTan x
            | LiyhArCsc x -> liyhArCsc x
            | LiyhArSec x -> liyhArSec x
            | LiyhArCot x -> liyhArCot x
            | LiyhSinh x -> liyhSinh x
            | LiyhCosh x -> liyhCosh x
            | LiyhTanh x -> liyhTanh x
            | LiyhCsch x -> liyhCsch x
            | LiyhSech x -> liyhSech x
            | LiyhCoth x -> liyhCoth x
            | LiyhArSinh x -> liyhArSinh x
            | LiyhArCosh x -> liyhArCosh x
            | LiyhArTanh x -> liyhArTanh x
            | LiyhArCsch x -> liyhArCsch x
            | LiyhArSech x -> liyhArSech x
            | LiyhArCoth x -> liyhArCoth x
            | LiyhSinc x -> liyhSinc x
            | LiyhAbs x -> liyhAbs x
            | LiyhSgn x -> liyhSgn x
            | LiyhDelta x -> liyhDelta x
            | LiyhCeil x -> liyhCeil x
            | LiyhFloor x -> liyhFloor x
            | LiyhRound x -> liyhRound x
            | LiyhId x -> liyhId x

        /// Evaluates the given elementary function numerically.
        let public evaluate (spEval: SumPow -> Constant) =
            function
            | InternalFunction.LiyhPow(base', exp) -> spEval base' ** spEval exp
            | InternalFunction.LiyhRoot(base', None) -> mapf sqrt (spEval base')
            | InternalFunction.LiyhRoot(base', Some exp) -> spEval base' ** (One / spEval exp)
            | InternalFunction.LiyhLog(arg, None) -> mapf log (spEval arg)
            | InternalFunction.LiyhLog(arg, Some base') -> mapf log (spEval arg) / mapf log (spEval base')
            | InternalFunction.LiyhSin(arg) -> mapf sin (spEval arg)
            | InternalFunction.LiyhExp(arg) -> mapf exp (spEval arg)
            | InternalFunction.LiyhCos(arg) -> mapf cos (spEval arg)
            | InternalFunction.LiyhTan(arg) -> mapf tan (spEval arg)
            | InternalFunction.LiyhCsc(arg) -> mapf (fun x -> 1.0 / sin x) (spEval arg)
            | InternalFunction.LiyhSec(arg) -> mapf (fun x -> 1.0 / cos x) (spEval arg)
            | InternalFunction.LiyhCot(arg) -> mapf (fun x -> 1.0 / tan x) (spEval arg)
            | InternalFunction.LiyhArSin(arg) -> mapf asin (spEval arg)
            | InternalFunction.LiyhArCos(arg) -> mapf acos (spEval arg)
            | InternalFunction.LiyhArTan(arg) -> mapf atan (spEval arg)
            | InternalFunction.LiyhArCsc(arg) -> mapf (fun x -> 1.0 / asin x) (spEval arg)
            | InternalFunction.LiyhArSec(arg) -> mapf (fun x -> 1.0 / acos x) (spEval arg)
            | InternalFunction.LiyhArCot(arg) -> mapf (fun x -> 1.0 / atan x) (spEval arg)
            | InternalFunction.LiyhSinh(arg) -> mapf sinh (spEval arg)
            | InternalFunction.LiyhCosh(arg) -> mapf cosh (spEval arg)
            | InternalFunction.LiyhTanh(arg) -> mapf tanh (spEval arg)
            | InternalFunction.LiyhCsch(arg) -> mapf (fun x -> 1.0 / sinh x) (spEval arg)
            | InternalFunction.LiyhSech(arg) -> mapf (fun x -> 1.0 / cosh x) (spEval arg)
            | InternalFunction.LiyhCoth(arg) -> mapf (fun x -> 1.0 / tanh x) (spEval arg)
            | InternalFunction.LiyhArSinh(arg) -> mapf (fun x -> log (sqrt (pown x 2 + 1.0) + x)) (spEval arg)
            | InternalFunction.LiyhArCosh(arg) -> mapf (fun x -> log (x + sqrt (x - 1.0) * sqrt (x + 1.0))) (spEval arg)
            | InternalFunction.LiyhArTanh(arg) -> mapf (fun x -> 0.5 * log (x + 1.0) - 0.5 * log (1.0 - x)) (spEval arg)
            | InternalFunction.LiyhSinc(arg) -> mapf (fun x -> if x = 0 then 1. else sin x / x) (spEval arg)
            | InternalFunction.LiyhAbs(arg) -> mapf abs (spEval arg)
            | InternalFunction.LiyhSgn(arg) -> mapf (double << sign) (spEval arg)
            | InternalFunction.LiyhDelta(Zero) -> Constant Double.PositiveInfinity
            | InternalFunction.LiyhDelta(x) -> mapf (fun a -> if a = 0. then Double.PositiveInfinity else 0) (spEval x)
            | InternalFunction.LiyhRound(x) -> mapf round (spEval x)
            | InternalFunction.LiyhCeil(x) -> mapf ceil (spEval x)
            | InternalFunction.LiyhFloor(x) -> mapf floor (spEval x)
            | InternalFunction.LiyhId(x) -> spEval x
            | other -> failwithf "Not implemented: %A" other

        /// Checks numerically whether the given floating-point number is an integer.
        let inline private isFInt (a: double) =
            abs (a % 1.) <= 1e-15  // It's a "dangerous" thing to do (IEEE), but we're waiting for something better.

        // Some predicate statements:

        let private f1 = ( = ) (Pi)             // x = π
        let private f2 = ( = ) (Pi / 2)         // x = π/2
        let private f3 = ( = ) (3 * Pi / 2)     // x = 3π/2
        let private f4 = ( = ) (2 * Pi)         // x = 2π
        let private f5 = ( = ) (Pi * I)         // x = πi
        let private f6 = ( = ) (2 * Pi * I)     // x = 2πi

        //
        //  We hard-code some of the identities associated with the elementary functions...
        //

        /// Algebraically simplifies `Sin[x]` elementary function.
        let private simplifydSin (x: SumPow) =
            match Simplification.simplify x with
            // sin(0) = 0
            | Zero -> Const Zero

            // sin(π/6) = 1/2
            | Frac(Pi, PureConstantExpressionInteger 6) -> Const One / Const 2

            // sin(π/4) = 1/√2
            | Frac(Pi, PureConstantExpressionInteger 4) -> Const One / liyhSqrt (Const 2)

            // sin(π/3) = √3/2
            | Frac(Pi, PureConstantExpressionInteger 3) -> liyhSqrt (Const 3) / 2

            // sin(π/2) = 1
            | Frac(Pi, PureConstantExpressionInteger 2) -> Const One

            // sin(π) = 0
            | Pi -> Const Zero

            // sin(nπ) = 0 for n∈Z
            | ProdWith1 f1 [ PureConstantExpressionInteger _, One ] -> Const Zero

            // sin(-x) = -sin(x)
            | Negative (factor, rest) -> -liyhSin (factor * rest)

            // sin(π/2 + x) = cos(x)
            | SumWith1 f2 x -> liyhCos (Sum (manyTermId x))

            // sin(π + x) = -sin(x)
            | SumWith1 f1 x -> -liyhSin (Sum (manyTermId x))

            // sin(3π/2 + x) = -cos(x)
            | SumWith1 f3 x -> -liyhCos (Sum (manyTermId x))

            // sin(2π + x) = sin(x)
            | SumWith1 f4 x -> liyhSin (Sum (manyTermId x))

            // sin(f⁻¹(x)) = ...
            | InternalFunction ifun ->
                match ifun with
                | LiyhArSin x -> x
                | LiyhArCos x -> liyhSqrt (1 - x ** 2)
                | LiyhArTan x -> x / liyhSqrt (1 + x ** 2)
                | LiyhArCsc x -> 1 / x
                | LiyhArSec x -> liyhSqrt (x ** 2 - 1) / x
                | LiyhArCot x -> 1 / liyhSqrt (1 + x ** 2)
                | ifun -> liyhSin (simplifyFunction ifun)

            | other -> liyhSin other

        /// Algebraically simplifies `Cos[x]` elementary function.
        let private simplifydCos (x: SumPow) =
            match Simplification.simplify x with
            // cos(0) = 1
            | Zero -> Const One

            // cos(π/6) = √3/2
            | Frac(Pi, PureConstantExpressionInteger 6) -> liyhSqrt (Const 3) / Const 2

            // cos(π/4) = 1/√2
            | Frac(Pi, PureConstantExpressionInteger 4) -> Const One / liyhSqrt (Const 2)

            // cos(π/3) = 1/2
            | Frac(Pi, PureConstantExpressionInteger 3) -> Const One / Const 2

            // cos(π/2) = 0
            | Frac(Pi, PureConstantExpressionInteger 2) -> Const Zero

            // cos(π) = -1
            | Pi -> Const -One

            // cos(2nπ) = 1 for n∈Z
            | ProdWith1 f4 [ PureConstantExpressionInteger _, One ] -> Const One

            // cos(-x) = cos(x)
            | Negative (factor, rest) -> liyhCos (factor * rest)

            // cos(π/2 + x) = -sin(x)
            | SumWith1 f2 x -> -liyhSin (Sum (manyTermId x))

            // cos(π + x) = -cos(x)
            | SumWith1 f1 x -> -liyhCos (Sum (manyTermId x))

            // cos(3π/2 + x) = sin(x)
            | SumWith1 f3 x -> liyhSin (Sum (manyTermId x))

            // cos(2π + x) = cos(x)
            | SumWith1 f4 x -> liyhCos (Sum (manyTermId x))

            // cos(f⁻¹(x)) = ...
            | InternalFunction ifun ->
                match ifun with
                | LiyhArSin x -> liyhSqrt (1 - x ** 2)
                | LiyhArCos x -> x
                | LiyhArTan x -> 1 / liyhSqrt (1 + x ** 2)
                | LiyhArCsc x -> liyhSqrt (x ** 2 - 1) / x
                | LiyhArSec x -> 1 / x
                | LiyhArCot x -> x / liyhSqrt (1 + x ** 2)
                | ifun -> liyhCos (simplifyFunction ifun)

            | other -> liyhCos other

        /// Algebraically simplifies `Tan[x]` elementary function.
        let private simplifydTan (x: SumPow) =
            match Simplification.simplify x with
            // tan(0) = 0
            | Zero -> Const Zero

            // tan(π/6) = 1/√3
            | Frac(Pi, PureConstantExpressionInteger 6) -> Const One / liyhSqrt (Const 3)

            // tan(π/4) = 1
            | Frac(Pi, PureConstantExpressionInteger 4) -> Const One

            // tan(π/3) = √3
            | Frac(Pi, PureConstantExpressionInteger 3) -> liyhSqrt (Const 3)

            // tan(π) = 0
            | Pi -> Const Zero

            // tan(nπ) = 0 for n∈Z
            | ProdWith1 f1 [ PureConstantExpressionInteger _, One ] -> Const Zero

            // tan(-x) = -tan(x)
            | Negative (factor, rest) -> -liyhTan (factor * rest)

            // tan(π/2 + x) = -cot(x)
            | SumWith1 f2 x -> -liyhCot (Sum (manyTermId x))

            // tan(π + x) = tan(x)
            | SumWith1 f1 x -> liyhTan (Sum (manyTermId x))

            // tan(3π/2 + x) = -cot(x)
            | SumWith1 f3 x -> -liyhCot (Sum (manyTermId x))

            // tan(2π + x) = tan(x)
            | SumWith1 f4 x -> liyhTan (Sum (manyTermId x))

            // tan(f⁻¹(x)) = ...
            | InternalFunction ifun ->
                match ifun with
                | LiyhArSin x -> x / liyhSqrt (1 - x ** 2)
                | LiyhArCos x -> liyhSqrt (1 - x ** 2) / x
                | LiyhArTan x -> x
                | LiyhArCsc x -> 1 / liyhSqrt (x ** 2 - 1)
                | LiyhArSec x -> liyhSqrt (x ** 2 - 1)
                | LiyhArCot x -> 1 / x
                | ifun -> liyhTan (simplifyFunction ifun)

            | other -> liyhTan other

        /// Algebraically simplifies `Csc[x]` elementary function.
        let private simplifydCsc (x: SumPow) =
            match Simplification.simplify x with
            // csc(π/6) = 2
            | Frac(Pi, PureConstantExpressionInteger 6) -> Const 2

            // csc(π/4) = √2
            | Frac(Pi, PureConstantExpressionInteger 4) -> liyhSqrt (Const 2)

            // csc(π/3) = 2/√3
            | Frac(Pi, PureConstantExpressionInteger 3) -> 2 / liyhSqrt (Const 3)

            // csc(π/2) = 1
            | Frac(Pi, PureConstantExpressionInteger 2) -> Const One

            // csc(-x) = -csc(x)
            | Negative (factor, rest) -> -liyhCsc (factor * rest)

            // csc(π/2 + x) = sec(x)
            | SumWith1 f2 x -> liyhSec (Sum (manyTermId x))

            // csc(π + x) = -csc(x)
            | SumWith1 f1 x -> -liyhCsc (Sum (manyTermId x))

            // csc(3π/2 + x) = -sec(x)
            | SumWith1 f3 x -> -liyhSec (Sum (manyTermId x))

            // csc(2π + x) = csc(x)
            | SumWith1 f4 x -> liyhCsc (Sum (manyTermId x))

            // csc(f⁻¹(x)) = ...
            | InternalFunction ifun ->
                match ifun with
                | LiyhArSin x -> 1 / x
                | LiyhArCos x -> 1 / liyhSqrt (1 - x ** 2)
                | LiyhArTan x -> liyhSqrt (x ** 2 + 1) / x
                | LiyhArCsc x -> x
                | LiyhArSec x -> 1 / liyhSqrt (1 - (1 / (x ** 2)))
                | LiyhArCot x -> liyhSqrt (1 / (x ** 2) + 1) * x
                | ifun -> liyhSin (simplifyFunction ifun)

            | other -> liyhCsc other

        /// Algebraically simplifies `Sec[x]` elementary function.
        let private simplifydSec (x: SumPow) =
            match Simplification.simplify x with
            // sec(0) = 1
            | Zero -> Const One

            // sec(π/6) = 2/√3
            | Frac(Pi, PureConstantExpressionInteger 6) -> Const One / Const 2

            // sec(π/4) = √2
            | Frac(Pi, PureConstantExpressionInteger 4) -> liyhSqrt (Const 2)

            // sec(π/3) = 2
            | Frac(Pi, PureConstantExpressionInteger 3) -> Const 2

            // sec(π) = -1
            | Pi -> Const -One

            // sec(2nπ) = 1 for n∈Z
            | ProdWith1 f4 [ PureConstantExpressionInteger _, One ] -> Const Zero

            // sec(-x) = sec(x)
            | Negative (factor, rest) -> liyhSec (factor * rest)

            // sec(π/2 + x) = -csc(x)
            | SumWith1 f2 x -> -liyhCsc (Sum (manyTermId x))

            // sec(π + x) = -sec(x)
            | SumWith1 f1 x -> -liyhSec (Sum (manyTermId x))

            // sec(3π/2 + x) = csc(x)
            | SumWith1 f3 x -> liyhCsc (Sum (manyTermId x))

            // sec(2π + x) = sec(x)
            | SumWith1 f4 x -> liyhSec (Sum (manyTermId x))

            // sec(f⁻¹(x)) = ...
            | InternalFunction ifun ->
                match ifun with
                | LiyhArSin x -> 1 / liyhSqrt (1 - x ** 2)
                | LiyhArCos x -> 1 / x
                | LiyhArTan x -> liyhSqrt (x ** 2 + 1)
                | LiyhArCsc x -> 1 / liyhSqrt (1 - (1 / (x ** 2)))
                | LiyhArSec x -> x
                | LiyhArCot x -> liyhSqrt (1 / (x ** 2) + 1)
                | ifun -> liyhSin (simplifyFunction ifun)

            | other -> liyhSec other

        /// Algebraically simplifies `Cot[x]` elementary function.
        let private simplifydCot (x: SumPow) =
            match Simplification.simplify x with
            // cot(π/6) = √3
            | Frac(Pi, PureConstantExpressionInteger 6) -> liyhSqrt (Const 3)

            // cot(π/4) = 1
            | Frac(Pi, PureConstantExpressionInteger 4) -> Const One

            // cot(π/3) = 1/√3
            | Frac(Pi, PureConstantExpressionInteger 3) -> 1 / liyhSqrt (Const 3)

            // cot(π/2) = 0
            | Frac(Pi, PureConstantExpressionInteger 2) -> Const Zero

            // cot(-x) = -cot(x)
            | Negative (factor, rest) -> -liyhCot (factor * rest)

            // cot(π/2 + x) = -tan(x)
            | SumWith1 f2 x -> -liyhTan (Sum (manyTermId x))

            // cot(π + x) = cot(x)
            | SumWith1 f1 x -> liyhCot (Sum (manyTermId x))

            // cot(3π/2 + x) = -tan(x)
            | SumWith1 f3 x -> -liyhTan (Sum (manyTermId x))

            // cot(2π + x) = cot(x)
            | SumWith1 f4 x -> liyhCot (Sum (manyTermId x))

            // cot(f⁻¹(x)) = ...
            | InternalFunction ifun ->
                match ifun with
                | LiyhArSin x -> liyhSqrt (1 - x ** 2) / x
                | LiyhArCos x -> x / liyhSqrt (1 - x ** 2)
                | LiyhArTan x -> 1 / x
                | LiyhArCsc x -> liyhSqrt (1 - 1 / (x ** 2)) * x
                | LiyhArSec x -> 1 / liyhSqrt (1 - 1 / (x ** 2)) * x
                | LiyhArCot x -> x
                | ifun -> liyhCot (simplifyFunction ifun)

            | other -> liyhCot other

        /// Algebraically simplifies `ArSin[x]` elementary function.
        let private simplifydArSin (x: SumPow) =
            match Simplification.simplify x with
            // arSin(0) = 0
            | Zero -> Const Zero

            // arSin(1) = π/2
            | One -> Pi / 2

            // arSin(-x) = -arSin(x)
            | Negative (factor, rest) -> -liyhArSin (factor * rest)

            | other -> liyhArSin other

        /// Algebraically simplifies `ArCos[x]` elementary function.
        let private simplifydArCos (x: SumPow) =
            match Simplification.simplify x with
            // arCos(0) = π/2
            | Zero -> Pi / 2

            // arCos(1) = 0
            | One -> Const Zero

            | other -> liyhArCos other

        /// Algebraically simplifies `ArTan[x]` elementary function.
        let private simplifydArTan (x: SumPow) =
            match Simplification.simplify x with
            // arTan(0) = 0
            | Zero -> Const Zero

            // arTan(-x) = -arTan(x)
            | Negative (factor, rest) -> -liyhTan (factor * rest)

            // arTan(1) = π/4
            | One -> Pi / 4

            | other -> liyhArTan other

        /// Algebraically simplifies `ArCsc[x]` elementary function.
        let private simplifydArCsc (x: SumPow) =
            match Simplification.simplify x with
            // arCsc(0) = 0
            | Zero -> Const Zero

            // arCsc(-x) = -arCsc(x)
            | Negative (factor, rest) -> -liyhArCsc (factor * rest)

            | other -> liyhArCsc other

        /// Algebraically simplifies `ArSec[x]` elementary function.
        let private simplifydArSec (x: SumPow) =
            liyhArSec (Simplification.simplify x)

        /// Algebraically simplifies `ArCot[x]` elementary function.
        let private simplifydArCot (x: SumPow) =
            match Simplification.simplify x with
            // arCot(0) = π/2
            | Zero -> Pi / 2

            // arCot(-x) = -arCot(x)
            | Negative (factor, rest) -> -liyhArCot (factor * rest)

            | other -> liyhArCot other

        /// Algebraically simplifies `Sinh[x]` elementary function.
        let private simplifydSinh (x: SumPow) =
            match Simplification.simplify x with
            // sinh(0) = 0
            | Zero -> Const Zero

            // sinh(nπi) = 0 for n∈Z
            | ProdWith1 f5 [ PureConstantExpressionInteger _, One ] -> Const Zero

            // sinh(-x) = -sinh(x)
            | Negative (factor, rest) -> -liyhSinh (factor * rest)

            // sinh(f⁻¹(x)) = ...
            | InternalFunction ifun ->
                match ifun with
                | LiyhArSinh x -> x
                | LiyhArCosh x -> liyhSqrt ((x - 1) / (x + 1)) * (x + 1)
                | LiyhArTanh x -> x / liyhSqrt (1 - x ** 2)
                | LiyhArCsch x -> 1 / x
                | LiyhArSech x -> (liyhSqrt ((1 - x) / (1 + x)) * (x + 1)) / x
                | LiyhArCoth x -> 1 / (liyhSqrt (1 - (1 / (x ** 2))) * x)
                | ifun -> liyhSinh (simplifyFunction ifun)

            | other -> liyhSinh other

        /// Algebraically simplifies `Cosh[x]` elementary function.
        let private simplifydCosh (x: SumPow) =
            match Simplification.simplify x with
            // cosh(0) = 1
            | Zero -> Const One

            // cosh(2nπi) = 1 for n∈Z
            | ProdWith1 f6 [ PureConstantExpressionInteger _, One ] -> Const One

            // cosh(-x) = cosh(x)
            | Negative (factor, rest) -> liyhCosh (factor * rest)

            // cosh(f⁻¹(x)) = ...
            | InternalFunction ifun ->
                match ifun with
                | LiyhArSinh x -> liyhSqrt (x ** 2 - 1)
                | LiyhArCosh x -> x
                | LiyhArTanh x -> 1 / liyhSqrt (1 - x ** 2)
                | LiyhArCsch x -> liyhSqrt (1 / (x ** 2) + 1)
                | LiyhArSech x -> 1 / x
                | LiyhArCoth x -> 1 / liyhSqrt (1 - (1 / (x ** 2)))
                | ifun -> liyhCosh (simplifyFunction ifun)

            | other -> liyhCosh other

        /// Algebraically simplifies `Tanh[x]` elementary function.
        let private simplifydTanh (x: SumPow) =
            match Simplification.simplify x with
            // tanh(0) = 0
            | Zero -> Const Zero

            // tanh(nπi) = 0 for n∈Z
            | ProdWith1 f5 [ PureConstantExpressionInteger _, One ] -> Const Zero

            // tanh(-x) = -tanh(x)
            | Negative (factor, rest) -> -liyhTanh (factor * rest)

            // tanh(f⁻¹(x)) = ...
            | InternalFunction ifun ->
                match ifun with
                | LiyhArSinh x -> x / liyhSqrt (x ** 2 + 1)
                | LiyhArCosh x -> (liyhSqrt ((x - 1) / (x + 1)) * (x + 1)) / x
                | LiyhArTanh x -> x
                | LiyhArCsch x -> 1 / (liyhSqrt (1 / (x ** 2) + 1) * x)
                | LiyhArSech x -> liyhSqrt ((1 - x) / (1 + x)) * (x + 1)
                | LiyhArCoth x -> 1 / x
                | ifun -> liyhTanh (simplifyFunction ifun)

            | other -> liyhTanh other

        /// Algebraically simplifies `Csch[x]` elementary function.
        let private simplifydCsch (x: SumPow) =
            match Simplification.simplify x with
            // csch(0) = 0
            | Zero -> Const Zero

            // csch(-x) = -csch(x)
            | Negative (factor, rest) -> -liyhCsch (factor * rest)

            // csch(f⁻¹(x)) = ...
            | InternalFunction ifun ->
                match ifun with
                | LiyhArSinh x -> 1 / x
                | LiyhArCosh x -> 1 / (liyhSqrt ((x - 1) / (x + 1)) * (x + 1))
                | LiyhArTanh x -> liyhSqrt (1 - x ** 2) / x
                | LiyhArCsch x -> x
                | LiyhArSech x -> x / (liyhSqrt ((1 - x) / (1 + x)) * (x + 1))
                | LiyhArCoth x -> liyhSqrt (1 + 1 / (x ** 2)) * x
                | ifun -> liyhCsch (simplifyFunction ifun)

            | other -> liyhCsch other

        /// Algebraically simplifies `Sech[x]` elementary function.
        let private simplifydSech (x: SumPow) =
            match Simplification.simplify x with
            // sech(0) = 1
            | Zero -> Const One

            // sech(nπi) = 1 for n∈Z
            | ProdWith1 f6 [ PureConstantExpressionInteger _, One ] -> Const One

            // sech(-x) = sech(x)
            | Negative (factor, rest) -> liyhSech (factor * rest)

            // sech(f⁻¹(x)) = ...
            | InternalFunction ifun ->
                match ifun with
                | LiyhArSinh x -> 1 / liyhSqrt (x ** 2 + 1)
                | LiyhArCosh x -> 1 / x
                | LiyhArTanh x -> liyhSqrt (1 - x ** 2)
                | LiyhArCsch x -> 1 / liyhSqrt (1 / (x ** 2) + 1)
                | LiyhArSech x -> x
                | LiyhArCoth x -> liyhSqrt (1 - 1 / (x ** 2))
                | ifun -> liyhSech (simplifyFunction ifun)

            | other -> liyhSech other

        /// Algebraically simplifies `Coth[x]` elementary function.
        let private simplifydCoth (x: SumPow) =
            match Simplification.simplify x with
            // coth(-x) = -coth(x)
            | Negative (factor, rest) -> -liyhCoth (factor * rest)

            // coth(f⁻¹(x)) = ...
            | InternalFunction ifun ->
                match ifun with
                | LiyhArSinh x -> liyhSqrt (x ** 2 + 1) / x
                | LiyhArCosh x -> x / (liyhSqrt ((x - 1) / (x + 1)) * (x + 1))
                | LiyhArTanh x -> 1 / x
                | LiyhArCoth x -> x
                | ifun -> liyhCoth (simplifyFunction ifun)

            | other -> liyhCoth other

        /// Algebraically simplifies `ArSinh[x]` elementary function.
        let private simplifydArSinh (x: SumPow) =
            match Simplification.simplify x with
            // arsinh(0) = 0
            | Zero -> Const Zero

            // arsinh(-x) = -arsinh(x)
            | Negative (factor, rest) -> -liyhArSinh (factor * rest)

            | other -> liyhArSinh other

        /// Algebraically simplifies `ArCosh[x]` elementary function.
        let private simplifydArCosh (x: SumPow) =
            match Simplification.simplify x with
            // arcosh(0) = iπ/2
            | Zero -> I * Pi / 2

            | other -> liyhArCosh other

        /// Algebraically simplifies `ArTanh[x]` elementary function.
        let private simplifydArTanh (x: SumPow) =
            match Simplification.simplify x with
            // artanh(0) = 0
            | Zero -> Const Zero

            // artanh(-x) = -artanh(x)
            | Negative (factor, rest) -> -liyhArTanh (factor * rest)

            | other -> liyhArTanh other

        /// Algebraically simplifies `ArCsch[x]` elementary function.
        let private simplifydArCsch (x: SumPow) =
            match Simplification.simplify x with
            // arcsch(0) = 0
            | Zero -> Const Zero

            // arcsch(-x) = -arcsch(x)
            | Negative (factor, rest) -> -liyhArCsch (factor * rest)

            | other -> liyhArCsch other

        /// Algebraically simplifies `ArSech[x]` elementary function.
        let private simplifydArSech (x: SumPow) =
            match Simplification.simplify x with
            // arsech(1) = 0
            | One -> Const Zero

            | other -> liyhArSech other

        /// Algebraically simplifies `ArCoth[x]` elementary function.
        let private simplifydArCoth (x: SumPow) =
            match Simplification.simplify x with
            // arcoth(0) = iπ/2
            | Zero -> I * Pi / 2

            // arcoth(-x) = -arcoth(x)
            | Negative (factor, rest) -> -liyhArCoth (factor * rest)

            | other -> liyhArCoth other

        /// Algebraically simplifies `Pow[b, p]` elementary function.
        let private simplifydPow (b: SumPow) (p: SumPow) =
            match Simplification.simplify b, Simplification.simplify p with
            | a, Fun("Log", [ x; b ]) -> if a = b then x else b ** p
            | b, p -> Simplification.simplify (b ** p)

        /// Algebraically simplifies `Root[x, nth]` elementary function.
        let private simplifydRoot (x: SumPow) (nth: SumPow option) =
            let x = Simplification.simplify x
            let nth = Option.defaultValue (Const 2) (Option.map Simplification.simplify nth)
            liyhRoot (x, nth)

        /// Algebraically simplifies `Log[x, b]` elementary function.
        let private simplifydLog (x: SumPow) (b: SumPow option) =
            let b = Option.defaultValue E b

            match Simplification.simplify x, Simplification.simplify b with
            | x, b when x = b -> Const One
            | One, _ -> Const Zero
            | _, Zero -> Const Zero
            | PureConstantExpressionInteger n, b when n <> 0 ->
                if n < 0 then liyhLog (Const (fromBigInt (abs n)), b) + I * Pi
                else
                    let targ =
                        match b with
                        | E -> Some (log (double n))
                        | PureConstantExpressionInteger b -> Some (log (double n) / log (double b))
                        | _ -> None

                    Option.defaultWith
                        (konst (liyhLog (Const n, b)))
                        (Option.bind (fun a -> if isFInt a then Some (Const a) else None) targ)

            | Power(x, p), b -> Simplification.simplify (p * liyhLog (x, b))
            | Prod prod, b ->
                let sm = List.map (fun (x, p) -> liyhLog (x ** p, b) |> Simplification.simplify) prod
                Sum (manyTermId sm)

            | x, b -> liyhLog (Simplification.simplify x, Simplification.simplify b)

        /// Algebraically simplifies `Abs[x]` elementary function.
        let private simplifydAbs (x: SumPow) =
            match Simplification.simplify x with
            | PureConstantExpressionInteger x -> Const (fromBigInt (abs x))
            | PureConstantExpressionFloat x -> Const (fromDouble (abs x))
            | PureConstantExpressionRational (num, den) ->
                Const (fromBigInt (abs num)) / Const (fromBigInt (abs den))
            | other -> liyhAbs other

        /// Algebraically simplifies `Sinc[x]` elementary function.
        let private simplifydSinc (x: SumPow) =
            match Simplification.simplify x with
            | Zero -> Const One // by definition (to make the function continious)
            | other ->
                let simp = Simplification.simplify other
                Simplification.simplify ((liyhSin simp) / simp)

        /// Algebraically simplifies `Sgn[x]` elementary function.
        let private simplifydSgn (x: SumPow) =
            match Simplification.simplify x with
            | PureConstantExpressionInteger x -> Const (sign x)
            | PureConstantExpressionFloat x -> Const (sign x)
            | PureConstantExpressionRational (num, den) -> Const (sign (num * den))
            | InternalFunction (LiyhSgn x) -> liyhSgn x
            | InternalFunction (LiyhAbs _) -> Const One
            | InternalFunction (LiyhRoot (_, Some (PureConstantExpressionNatural nth))) when nth % 2 = 0 -> Const One
            | other -> liyhSgn other

        /// Algebraically simplifies `δ[x]` "elementary function".
        let private simplifydDelta (x: SumPow) =
            match Simplification.simplify x with
            | PureConstantExpression pc when not (Misc.isZero pc) -> Const Zero
            | x -> liyhDelta x

        /// Algebraically simplifies `Ceil[x]` elementary function.
        let private simplifydCeil (x: SumPow) =
            match Simplification.simplify x with
            | PureConstantExpressionInteger x -> Const (fromBigInt x)
            | PureConstantExpressionFloat x -> Const (Constant (ceil x))
            | PureConstantExpressionRational (num, den) -> Const (Constant (ceil (double num / double den)))
            | Negative (factor, rest) -> liyhFloor (factor * rest)
            | other -> liyhCeil other

        /// Algebraically simplifies `Floor[x]` elementary function.
        let private simplifydFloor (x: SumPow) =
            match Simplification.simplify x with
            | PureConstantExpressionInteger x -> Const (fromBigInt x)
            | PureConstantExpressionFloat x -> Const (Constant (floor x))
            | PureConstantExpressionRational (num, den) -> Const (Constant (floor (double num / double den)))
            | Negative (factor, rest) -> liyhCeil (factor * rest)
            | other -> liyhFloor other

        /// Algebraically simplifies `Round[x]` elementary function.
        let private simplifydRound (x: SumPow) =
            match Simplification.simplify x with
            | PureConstantExpressionInteger x -> Const (fromBigInt x)
            | PureConstantExpressionFloat x -> Const (fromDouble (round x))
            | PureConstantExpressionRational (num, den) -> Const (fromDouble (round (double num / double den)))
            | Negative (factor, rest) -> -liyhRound (factor * rest)
            | other -> liyhRound other

        /// Algebraically simplifies elementary functions when particular arguments or identities match.
        let public simplifyFunction =
            function

            // Power and logarithm functions.

            | LiyhPow(b, p) -> simplifydPow b p
            | LiyhRoot(x, nth) -> simplifydRoot x nth
            | LiyhLog(x, b) -> simplifydLog x b
            | LiyhExp x -> simplifyFunction (LiyhPow (E, x))

            // Trigonometric functions.

            | LiyhSin x -> simplifydSin x
            | LiyhCos x -> simplifydCos x
            | LiyhTan x -> simplifydTan x
            | LiyhCsc x -> simplifydCsc x
            | LiyhSec x -> simplifydSec x
            | LiyhCot x -> simplifydCot x

            // Inverse trigonometric functions.

            | LiyhArSin x -> simplifydArSin x
            | LiyhArCos x -> simplifydArCos x
            | LiyhArTan x -> simplifydArTan x
            | LiyhArCsc x -> simplifydArCsc x
            | LiyhArSec x -> simplifydArSec x
            | LiyhArCot x -> simplifydArCot x

            // Hyperbolic functions.

            | LiyhSinh x -> simplifydSinh x
            | LiyhCosh x -> simplifydCosh x
            | LiyhTanh x -> simplifydTanh x
            | LiyhCsch x -> simplifydCsch x
            | LiyhSech x -> simplifydSech x
            | LiyhCoth x -> simplifydCoth x

            // Inverse hyperbolic functions.

            | LiyhArSinh x -> simplifydArSinh x
            | LiyhArCosh x -> simplifydArCosh x
            | LiyhArTanh x -> simplifydArTanh x
            | LiyhArCsch x -> simplifydArCsch x
            | LiyhArSech x -> simplifydArSech x
            | LiyhArCoth x -> simplifydArCoth x

            // Miscellaneous functions.

            | LiyhSinc x -> simplifydSinc x
            | LiyhAbs x -> simplifydAbs x
            | LiyhSgn x -> simplifydSgn x
            | LiyhDelta x -> simplifydDelta x
            | LiyhCeil x -> simplifydCeil x
            | LiyhFloor x -> simplifydFloor x
            | LiyhRound x -> simplifydRound x
            | LiyhId x -> Simplification.simplify x

        // -- Some patterns for internal functions -- //

        let public (|Exp|_|) =
            function
            | Power(Name "e", p) -> Some p
            | Fun("Exp", [ arg ]) -> Some arg
            | _ -> None

        let public (|Log|_|) =
            function
            | Fun("Log", [ x; b ]) -> Some (x, b)
            | Fun("Log", [ x ]) -> Some (x, Const 10)
            | Fun("Ln", [ x ]) -> Some (x, Name "E")
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
        open PureConstantExpression
        open System.Collections.Generic

        exception public UnboundVariableException of vname: string
        exception public UnboundFunctionException of fname: string
        exception public ExpressionCannotBeConvertedToLambdaException of expr: SumPow

        /// Determine whether the two expressions are numerically approximately equal up to the given precision. If `eps` is `None`
        /// then the comparison is made with a fixed femto-precision (`1e-15`).
        let public approximatelyEquals (sp1: SumPow) (sp2: SumPow) (values: IDictionary<string, Constant>) (eps: double voption) =
            Constant.approximatelyEquals (evaluate sp1 values) (evaluate sp2 values) eps

        /// Determine whether the given expressions is numerically approximately equal to zero up to the given precision.
        /// If `eps` is `None` then the comparison is made with a fixed femto-precision (`1e-15`).
        let public approximatelyEqualsZero (sp: SumPow) (eps: double voption) =
            approximatelyEquals sp (Const Zero) (dict []) eps

        /// Evaluates the given expression by replacing each variable found with its given value. Note: The calculation is
        /// subject to `double` capabilities. This function might throw an exception if some variables are not assigned.
        let public evaluate (sp: SumPow) (values: IDictionary<string, Constant>) =
            let varFreeExpression = Subst.manySubstVarConst values sp

            let rec inner =
                function

                // Common constants
                | Pattern.Pi -> Constant Math.PI
                | Pattern.E -> Constant Math.E

                // Numeric constants
                | Const cst -> cst

                | Frac(a, b) -> inner a / inner b
                | Power(b, p) -> inner b ** inner p
                | Sum xs -> List.fold (fun acc a -> acc + evalTerm a) Zero xs
                | InternalFunction.InternalFunction f -> InternalFunction.evaluate inner f
                | Fun(fname, _) -> raise (UnboundFunctionException fname)

                // If a variable has not been referenced, an exception is thrown.
                | Name name -> raise (UnboundVariableException name)

            and evalTerm (Term prod) = List.fold (fun acc a -> acc * evalPow a) One prod
            and evalPow (Pow(b, p)) = inner b ** inner p

            inner varFreeExpression

        /// Assuming the expression contains only constants, returns the approximate result of the expression.
        let public evaluate0 (sp: SumPow) =
            evaluate sp (dict [])

        /// Assuming that the expression contains only one variable, return the result of the constant expression
        /// approximated, replacing the variable with the given value.
        let inline public evaluate1 (sp: SumPow) (variable: string) (value: Constant) =
            evaluate sp (dict [ variable, value ])

        /// Given an expression and a variable, returns a lambda `double -> double`. This makes univariate numerical
        /// evaluations more convenient to work with since we will no longer be dependent on `evaluate1`.
        /// Note: throws an exception if there are incompatibilities with the variable involved.
        let inline public makef1 (expr: SumPow) (variable: string) =
            let expressionVariables = Misc.listVariables expr
            if not (List.isEmpty expressionVariables) && expressionVariables <> [ variable ] then
                raise (ExpressionCannotBeConvertedToLambdaException expr)

            let expr = partialEval expr
            fun (value: double) ->
                evaluate1 expr variable (Constant value) |> toDouble

        /// Generates an array of Constant numerical values from `min` to `max` in `step` increments.
        let public generatePoints1D (min: double) (max: double) (step: double) (sp: SumPow) (variable: string) =
            let xs = [| Constant min .. Constant step .. Constant max |]
            Array.Parallel.map (evaluate1 sp variable) xs

        /// Generates a set of values, from `min` to `max` in `step` increments, to be used in a graph plotting.
        /// Each new array corresponds to a new part of the graph separated by an asymptote.
        let public generateGraph (min: double) (max: double) (step: double) (sp: SumPow) (variable: string) =
            let fn = makef1 sp variable

            let xs = [| min .. step .. max |]
            let ys = Array.Parallel.map fn xs
            let points = Array.Parallel.zip xs ys

            // Detect if a point is pathological (e.g., infinity or NaN).
            let isPathological =
                snd >> Double.IsFinite >> not

            /// Calculates the standard deviation of the set of given values.
            let stdDev (values: double array) =
                let values = Array.Parallel.filter Double.IsFinite values
                let mean = Array.Parallel.average values

                values
                |> Array.Parallel.map (fun v -> pown (v - mean) 2)
                |> Array.Parallel.average
                |> sqrt

            // The threshold at which a value is "statistically" considered to be too far from the previous points
            // for the function to be considered smooth / continuous / behaving well locally at a point in question
            let threshold = stdDev ys

            // Determines whether the two points are too far apart in terms of standard deviation from the overall mean.
            let inline isJumpTooLarge y1 y2 =
                abs (y2 - y1) > threshold

            // If the subgraph contains more than one point, it is added to the global graph.
            let inline mayAppend current acc =
                if List.length current > 1 then current :: acc else acc

            // Split the list of points into sublists, separated by pathological points or large jumps.
            let rec splitPoints acc current prevY =
                function
                | [] -> mayAppend current acc

                | (x, y) :: rest when (isPathological (x, y) || (Option.exists (isJumpTooLarge y) prevY)) ->
                    match current with
                    | [] -> splitPoints acc [] None rest
                    | _ -> splitPoints (mayAppend current acc) [] None rest

                | (x, y) :: rest ->
                    splitPoints acc ((x, y) :: current) (Some y) rest

            Array.toList points
            |> splitPoints [] [] None
            |> List.map List.toArray
            |> Array.ofList

        /// Generates an array of Constant numerical 2D points from `min` to `max` in `step` increments.
        let public generatePoints2D (min: double) (max: double) (step: double) (sp: SumPow) (variable: string) =
            let xs = [| Constant min .. Constant step .. Constant max |]
            let ys = Array.Parallel.map (evaluate1 sp variable) xs
            Array.zip xs ys |> Array.filter (function Constant x, Constant y -> Double.IsFinite y)

        /// Partially evaluates the given expression, only calculating the constant expressions numerically.
        /// For example `3x/4 - 1` will give `0.75x - 1`.
        let public partialEval (sp: SumPow) =

            let inline partialEvalPow (Pow (b, p)) =
                match partialEval b, partialEval p with
                | Const b, Const p -> Const (b ** p)
                | b, p -> b ** p

            let inline partialEvalTerm (Term term) =
                let z = List.map partialEvalPow term
                let cs, ncs = List.partition (function Const _ -> true | _ -> false) z
                List.fold ( * ) (Const One) ncs * List.fold ( * ) (Const One) cs

            let inline partialEvalSum (sum: Term list) =
                let z = List.map partialEvalTerm sum
                let cs, ncs = List.partition (function Const _ -> true | _ -> false) z
                List.fold ( + ) (Const Zero) ncs + List.fold ( + ) (Const Zero) cs

            let rec peval =
                function
                | PureConstantExpression pc -> Const (evaluate0 pc)
                | Sum sum -> partialEvalSum sum
                | Fun(fname, args) -> Fun(fname, List.map partialEval args)
                | other -> other

            Simplification.simplify (peval sp)

        /// Partially evaluates the given expression, only calculating the constant expressions numerically after expand.
        /// For example, `4x*(Sqrt[2]/5 + x/3)` will give `1.1313x + x²1.3333`.
        let public partialEvalExpand = Expand.fullExpand >> partialEval

    /// Extends the field of reals (modeled by SumPow) to the field of complexes.
    module public Complex =
        open PureConstantExpression
        open InternalFunction
        open SimplifiedSum

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
            | SimplifiedSum [ [ Cos x, One ]; [ (ImaginaryUnit, PureConstantExpressionInteger n); Sin x', One ] ]
            | SimplifiedSum [ [ Cos x, One ]; [ Sin x', One ; (ImaginaryUnit, PureConstantExpressionInteger n)] ]
            | SimplifiedSum [ [ Sin x', One; (ImaginaryUnit, PureConstantExpressionInteger n) ]; [ Cos x, One ] ]
            | SimplifiedSum [ [ (ImaginaryUnit, PureConstantExpressionInteger n); Sin x', One ]; [ Cos x, One ] ]
                when (x = x') && ((n % 4) = 1) -> Some x

            | _ -> None

        /// Returns the principal argument of the given complex number.
        let public arg =
            Simplification.simplify << function
            | ComplexSumPow.PolarForm (_, angle) -> angle
            | ComplexSumPow.VectorForm (a, b) ->
                if not (Misc.isZero a) && not (Misc.isZero b) then liyhArTan (b / a)
                elif Misc.isZero a then liyhArSin (Const One)
                elif Misc.isZero b then liyhArCos (Const One)
                else ElementaryOperations.divByZero a

        /// Return the norm of the given complex number.
        let public norm =
            Simplification.simplify << function
            | ComplexSumPow.PolarForm (r, _) -> r
            | ComplexSumPow.VectorForm (a, b) -> liyhSqrt (a ** 2 + b ** 2)

        /// Matches an expression that reduces to the imaginary unit. The expression `Sqrt[-1]` is a dangerous abuse
        /// of notation that is not implemented as a representation of `i`.
        let public (|ImaginaryUnit|_|) =
            function

            // Trivial case: i = i.
            | i when i = imaginaryUnitNotation -> Some ()

            // i^(4n + 1) ≡ i
            | Power (ImaginaryUnit, PureConstantExpressionInteger n) when (n % 4) = 1 -> Some ()

            // Cis[pi/2] ≡ Cos[pi/2] + iSin[pi/2] ≡ Exp[iπ/2] ≡ i
            | Cis (Frac (Name "pi", PureConstantExpressionInteger 2)) -> Some ()

            | _ -> None

        /// Pattern-match a purely imaginary complex number of the form `(a + bi)` where `a = 0`, and if so return `b`.
        let private (|PureImaginary|_|) =
            convertToVectorForm >> function
            | ComplexSumPow.VectorForm (Zero, b) -> if Misc.isZero b then None else Some b
            | _ -> None

        /// Pattern-match a purely real complex number of the form `(a + bi)` where `b = 0`, and if so return `a`.
        let private (|PureReal|_|) =
            convertToVectorForm >> function
            | ComplexSumPow.VectorForm (a, Zero) -> if Misc.isZero a then None else Some a
            | _ -> None

        /// Check whether the given expression corresponds to the imaginary unit `i`.
        let public isImaginaryUnit =
            function
            | ImaginaryUnit _ -> true
            | _ -> false

        [<RequireQualifiedAccess>]
        type public ComplexSumPow =

            /// Complex expression of the form `z = a + ib`
            | VectorForm of re: SumPow * im: SumPow

            /// Complex expression of the form `z(r, ϑ) = r⋅Exp[iϑ]` where `r` is the radius and `ϑ` is the angle.
            | PolarForm of radius: SumPow * angle: SumPow

            static member op_Addition(a: ComplexSumPow, b: ComplexSumPow) = complexAddition (a, b)
            static member op_Subtraction(a: ComplexSumPow, b: ComplexSumPow) = complexSubtraction (a, b)
            static member op_Multiply(a: ComplexSumPow, b: ComplexSumPow) = complexMultiplication (a, b)
            static member op_Division(a: ComplexSumPow, b: ComplexSumPow) = complexDivision (a, b)
            static member Pow(a: ComplexSumPow, b: ComplexSumPow) = complexPower (a, b)
            static member op_UnaryNegation(a: ComplexSumPow) = complexNegation a

        /// Convert a complex number to the form `a + bi`.
        let public convertToVectorForm =
            simplifyComplex << function
            | ComplexSumPow.VectorForm _ as z -> z
            | ComplexSumPow.PolarForm(radius, angle) ->
                ComplexSumPow.VectorForm(radius * Fun("Cos", [ angle ]), radius * Fun("Sin", [ angle ]))

        /// Convert a complex number to the form `re^(iφ)`.
        let public convertToPolarForm =
            simplifyComplex << function
            | ComplexSumPow.PolarForm _ as z -> z
            | ComplexSumPow.VectorForm (re, im) as z ->
                let r = liyhSqrt (re ** 2 + im ** 2)
                let ϑ = arg z
                
                ComplexSumPow.PolarForm (r, ϑ)

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

        let private complexNegation =
            function
            | ComplexSumPow.VectorForm(re, im) -> ComplexSumPow.VectorForm(-re, -im)
            | ComplexSumPow.PolarForm(radius, angle) -> ComplexSumPow.PolarForm(-radius, angle)

        let private complexPower =
            simplifyComplex << function
            | z1, PureReal (PureConstantExpressionInteger n) ->
                let r, θ = norm z1, arg z1
                let r', θ' = (r ** n), (n * θ)

                let re = r' * liyhCos θ'
                let im = r' * liyhSin θ'

                ComplexSumPow.VectorForm(re, im)

            // The two cases are totally equivalent, but depending on the power argument, it's useful to
            // switch from one case to the other, this potentially means one less conversion.

            | z1, ComplexSumPow.VectorForm (c, d) ->
                let radius, angle = norm z1, arg z1
                let e1 = c * liyhLn radius - d * angle
                let e2 = d * liyhLn radius + c * angle
                ComplexSumPow.PolarForm (liyhExp e1, e2)

            | z1, ComplexSumPow.PolarForm (r2, θ2) ->
                let r1, θ1 = norm z1, arg z1
                let l = liyhLn r1
                ComplexSumPow.PolarForm (liyhExp (r2 * l - θ2 * θ1), r2 * θ1 + θ2 * l)  

        /// Use `Simplification.Simplify` on each `SumPow` component part of the given complex number.
        let public simplifyComplex =
            function
            | ComplexSumPow.PolarForm (r, θ) ->
                ComplexSumPow.PolarForm (Simplification.simplify r, Simplification.simplify θ)

            | ComplexSumPow.VectorForm (a, b) ->
                ComplexSumPow.VectorForm (Simplification.simplify a, Simplification.simplify b)

        let public complexZero =
            ComplexSumPow.VectorForm (Const Zero, Const Zero)

        let public complexOne =
            ComplexSumPow.VectorForm (Const One, Const One)

        let inline private justRe x = ComplexSumPow.VectorForm(x, Const Zero)
        let inline private justIm x = ComplexSumPow.VectorForm(Const Zero, x)
        let inline private complex re im = ComplexSumPow.VectorForm(re, im)
        let inline private cis arg = complex (liyhCos arg) (liyhSin arg)

        let private expnImg (n: int) =
            match n % 4 with
            | 0 -> Const 1
            | 1 -> imaginaryUnitNotation
            | 2 -> Const -1
            | 3 -> -imaginaryUnitNotation
            | _ -> failwith "Unexpected case"

        /// Calculate the complex conjugate of the given complex number.
        let rec public conjugate =
            function
            | ComplexSumPow.VectorForm (re, im) -> ComplexSumPow.VectorForm (re, -im)
            | ComplexSumPow.PolarForm (r, θ) -> ComplexSumPow.PolarForm (r, -θ)

        /// Convert a SumPow into a complex number. It is recommended to use the pseudo-function `Complex[a, b]` to express
        /// complex numbers via SumPow, but if an imaginary unit `i` is detected in the SumPow expression, this `asComplex`
        /// function should be able to incorporate it into the conversion.
        let public asComplex =
            function
            | Fun("Complex", [ re; im ]) -> complex re im
            | Cis arg -> cis arg
            | ImaginaryUnit -> justIm (Const One)
            | (Const _ as sp) | (Name _ as sp) | (Fun _ as sp) -> justRe sp // TODO: converting standard functions to complex!
            | Power(ImaginaryUnit, PureConstantExpressionInteger n) -> asComplex (expnImg n)
            | Power(a, b) -> asComplex a ** asComplex b
            | ProdWith1 isImaginaryUnit x -> justIm (Misc.prodToSumPow x)
            | Prod prod -> List.fold (fun acc (b, p) -> acc * asComplex (b ** p)) complexOne prod
            | SumList sl -> List.fold (fun acc z -> acc + asComplex z) complexZero sl
    
        /// Deduce whether the given complex number is purely real.
        let public isPureReal =
            function
            | PureReal _ -> true
            | _ -> false
        
        /// Deduce whether the given complex number is purely imaginary.
        let public isPureImaginary =
            not << isPureReal

        /// Deduce whether the given SumPow expression is purely real.
        let public isPureRealSumPow =
            asComplex >> isPureReal

        /// Deduce whether the given SumPow expression is purely imaginary.
        let public isPureImaginarySumPow =
            asComplex >> isPureImaginary

        /// Active pattern for pure complex numbers (not real numbers).
        let public (|ComplexSumPow|_|) (sp: SumPow) =
            match asComplex sp with
            | PureReal _ -> None
            | complex -> Some complex

        /// Convert the SumPow representation into the SumPow representation extended to complexes,
        /// i.e. the SumPow expression is translated in the form `Complex[re, im]`.
        let public sumPowAsComplexSumPowFunction =
            asComplex >> asSumPowFunction

        /// Convert the given complex number into a SumPow expression of the form `a + bi`.
        let public asSumPowVecExpression (z: ComplexSumPow) =
            let (ComplexSumPow.VectorForm(re, im)) = convertToVectorForm z
            re + (imaginaryUnitNotation * im)

        /// Convert the given complex number into a SumPow expression of the form `re^(iφ)`.
        let public asSumPowExpExpression (z: ComplexSumPow) =
            let (ComplexSumPow.PolarForm(r, φ)) = convertToPolarForm z
            r * liyhExp (imaginaryUnitNotation * φ)

        /// Convert the given complex number into the SumPow pseudo-function `Complex[a, b]`.
        /// That's the recommended way (because it's much easier to identify afterwards).
        let public asSumPowFunction (z: ComplexSumPow) =
            let (ComplexSumPow.VectorForm(re, im)) = convertToVectorForm z
            Fun ("Complex", [ re; im ])

        module public NumericEvaluation =
            open System.Collections.Generic

            /// Evaluates the given expression by replacing each variable found with its given value. Note: The calculation
            /// is subject to `double` capabilities. This function might throw an exception if some variables are not assigned.
            let public evaluate (csp: ComplexSumPow) (values: IDictionary<string, Constant>) =
                match convertToVectorForm csp with
                | ComplexSumPow.VectorForm (a, b) ->
                    SumPow.NumericEvaluation.evaluate a values, SumPow.NumericEvaluation.evaluate b values
                | _ -> failwith "??" // May not happen

            /// Evaluates the given expression by replacing each variable found with its given value. Note: The calculation is
            /// subject to `double` capabilities. This function might throw an exception if some variables are not assigned.
            let public evaluate0 (csp: ComplexSumPow) =
                evaluate csp (dict [])

            /// Assuming that the expression contains only one variable, return the result of the constant expression
            /// approximated, replacing the variable with the given value.
            let inline public evaluate1 (csp: ComplexSumPow) (variable: string) (value: Constant) =
                evaluate csp (dict [ variable, value ])

            /// Generates an array of Constant numerical 2D points from `min` to `max` in `step` increments.
            let public generatePoints2D (min: double) (max: double) (step: double) (csp: ComplexSumPow) (variable: string) =
                let xs = [| Constant min .. Constant step .. Constant max |]
                let ys = Array.Parallel.map (evaluate1 csp variable) xs
                
                Array.zip xs ys
                |> Array.filter (function (_, (Constant re, Constant im)) -> Double.IsFinite re && Double.IsFinite im)
                |> Array.map (function (Constant x, (Constant re, Constant im)) -> x, (re, im))

    [<RequireQualifiedAccess>]
    module public ModularArithmetic =
        open ElementaryOperations
        open PureConstantExpression

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
                member this.ToMathRender() = Some (toMathRender this)
                member this.ToMathRenderOrString() = Choice1Of2 (toMathRender this)

        let private toMathRender { number = number; modulus = modulus } =
            MathRenderHelper.parens (toMathRenderValue number)
            ++ MathRenderHelper.symbol ";"
            ++ MathRenderHelper.parens (MathRenderHelper.simpleText "mod" ++ MathRenderHelper.number modulus)

        let private toSymbolic { number = number; modulus = modulus } =
            let snum = Atomic.toSymbolic number
            let smod = atom (Atomic.Const modulus)

            { atom = Atom.Identifier "ModularNumber"
              attributes = [ ("number", snum); ("modulus", smod) ] }

        let private toSumPow { number = number; modulus = modulus } =
            if Misc.isZero number then Const Zero
            else Fun("ModularNumber", [ number; Const (double modulus) ])

        let private congruence { number = number; modulus = modulus } =
            match number with
            | PureConstantExpressionInteger number -> { number = Const (double (number % modulus)); modulus = modulus }
            | number -> { number = number; modulus = modulus }

        let public (|ModularNumber|_|) =
            function
            | Fun("ModularNumber", [ number; PureConstantExpressionInteger modulus ]) ->
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

    /// Heuristics for equality testing.
    [<RequireQualifiedAccess>]
    module public EqualityTest =
        open System.Collections.Generic

        exception public NumericallyDivergentExpressionException of SumPow

        // The limit is of arbitrary size; of course, the higher it is, the slower the test function
        // will be, but it's also less reliable.
        let private maxIteration = 150

        // We want to generate a number in a relevant range, with significant digits preserved.
        let private bounds = (-10e-14, +10e+14)

        /// Returns the mean and variance of the given table of values. 
        let private meanAndVariance (values: double[]) =
            let mutable sum = 0.0
            let mutable sumOfSquares = 0.0
            let n = double (Array.length values)

            for x in values do
                sum <- sum + x
                sumOfSquares <- sumOfSquares + pown x 2

            let mean = sum / n
            let variance = (sumOfSquares / n) - (pown mean 2)

            (mean, variance)

        /// Tests whether the two given expressions are equal.
        /// 
        /// This method is not symbolic, but uses numerical and statistical heuristics, so it cannot guarantee the "truth".
        /// Since this method doesn't perform any canonical transformations, it's generally faster than symbolic equality,
        /// testing and therefore also applies to an unlimited number of cases.
        let public equalityTest (sp1: SumPow) (sp2: SumPow) =
            let expr = NumericEvaluation.partialEval (sp1 - sp2) // This reduces the cost of subsequent calculations.
            let variables = Array.ofList (Misc.listVariables expr)

            // If the expression is purely numerical then there's no need to run all the machinery.
            if Array.isEmpty variables then
                NumericEvaluation.approximatelyEqualsZero expr ValueNone else

            let rnd = Random.Shared

            let inline initializer _ =
                let rec randomEvaluation (count: int) =

                    // If the expression to be tested returns an undefined value too many times, we throw an exception.
                    // In practice, this might be very rare.
                    if count >= maxIteration then
                        raise (NumericallyDivergentExpressionException expr)

                    let dc = Array.map (fun a -> a, Constant(rnd.NextDoubleLogarithmic bounds)) variables

                    match NumericEvaluation.evaluate expr (dict dc) with
                    | Constant n when not (Double.IsFinite n) -> randomEvaluation (count + 1)
                    | Constant n -> n

                randomEvaluation 0

            let rtable = Array.Parallel.init maxIteration initializer
            let m, v = meanAndVariance rtable

            // The mean of the values should be approximately zero, and the separation of these
            // values from the mean should also be close to zero for the result to be `true`.

            Math.approximatelyEquals m 0.0 ValueNone && Math.approximatelyEquals v 0.0 ValueNone

        /// Using the `equalityTest` heuristic, check if the given expression equals zero. This function is memoized.
        let public equalsZero =
            memoize (equalityTest (Const Zero))

    module public Rewrite =
        open SimplifiedSum
        open UnionFind

        type public Id = int

        type public ENode =
            | NameNode of string
            | ConstNode of Constant
            | SumNode of (Id * Id) list list
            | FunNode of string * Id list

        type public EClass =
            { id: Id
              nodes: Set<ENode>
              parents: Set<Id> }

        type public UF = UnionFind<Id> //  /!\ c'est mutable, est-ce que ça pose problème ? Normalement non si bien utilisé

        type public EGraph =
            { classes: Map<Id, EClass>
              unionFind: UF
              nextId: Id }

        let public emptyEGraph =
            { classes = Map.empty
              unionFind = UF Seq.empty
              nextId = 0 }

        let rec public addClass (nodes: ENode list) (egraph: EGraph) =
            let newClass =
                { id = egraph.nextId
                  nodes = Set.ofList nodes
                  parents = Set.empty }

            { classes = Map.add egraph.nextId newClass egraph.classes
              unionFind = egraph.unionFind
              nextId = egraph.nextId + 1 }

        let public findClass (id: Id) (egraph: EGraph) =
            let rootId = UnionFind.find egraph.unionFind id
            Map.find rootId egraph.classes

        let rec findEquivalentNode (node: ENode) (egraph: EGraph) =
            // Parcourt toutes les classes pour trouver un nœud équivalent
            egraph.classes
            |> Map.tryPick (fun id eclass ->
                if Set.exists (structurallyEqual node) eclass.nodes then
                    Some id
                else None)

        and structurallyEqual node1 node2 =
            match node1, node2 with
            | NameNode n1, NameNode n2 -> n1 = n2
            | ConstNode c1, ConstNode c2 -> c1 = c2
            | FunNode(name1, args1), FunNode(name2, args2) -> 
                name1 = name2 && List.length args1 = List.length args2
            | SumNode terms1, SumNode terms2 ->
                // Comparaison des termes (peut être améliorée selon les besoins)
                terms1 = terms2
            | _ -> false

        let addClass' (nodes: ENode list) (egraph: EGraph) =
            match nodes with
            | [node] ->
                // Cherche d'abord un nœud équivalent
                match findEquivalentNode node egraph with
                | Some existingId -> 
                    existingId, egraph
                | None ->
                    let newGraph = addClass nodes egraph
                    newGraph.nextId - 1, newGraph
            | _ -> 
                let newGraph = addClass nodes egraph
                newGraph.nextId - 1, newGraph

        let public merge (id1: Id) (id2: Id) (egraph: EGraph) =
            let root1 = UnionFind.find egraph.unionFind id1
            let root2 = UnionFind.find egraph.unionFind id2

            if root1 = root2 then egraph else

            let class1 = Map.find root1 egraph.classes
            let class2 = Map.find root2 egraph.classes

            let mergedNodes = Set.union class1.nodes class2.nodes
            let mergedParents = Set.union class1.parents class2.parents

            let newClass =
                { id = root1
                  nodes = mergedNodes
                  parents = mergedParents }

            let _ = UnionFind.connect egraph.unionFind root1 root2

            { egraph with
                classes = Map.add root1 newClass (Map.remove root2 egraph.classes) }

        (*

                let rec public addSumPow (egraph: EGraph) =
                    function
                    | Name name ->
                        let node = NameNode name
                        let egraph' = addClass [ node ] egraph
                        (egraph'.nextId - 1, egraph')

                    | Const constant ->
                        let node = ConstNode constant
                        let egraph' = addClass [ node ] egraph
                        (egraph'.nextId - 1, egraph')

                    | SimplifiedSum ssum ->
                        let inline folderPow (acc, g0) (b, p) =
                            let id1, g1 = addSumPow g0 b
                            let id2, g2 = addSumPow g1 p
                            ((id1, id2) :: acc, g2)

                        let inline folderTerm (acc, g) term =
                            let termResult, g' = List.fold folderPow ([], g) term
                            (termResult :: acc, g')

                        let ids, egraph' = List.fold folderTerm ([], egraph) ssum
                        let node = SumNode ids

                        let egraph' = addClass [ node ] egraph'
                        (egraph'.nextId - 1, egraph')

                    | Fun (name, args) ->
                        let folder (ids, g) sp =
                            let (newId, newG) = addSumPow g sp
                            (newId :: ids, newG)

                        let (argIds, egraph') = List.fold folder ([], egraph) args
                        let node = FunNode(name, List.rev argIds)
                        let egraph' = addClass [ node ] egraph'
                        (egraph'.nextId - 1, egraph')
        *)

        let rec public addSumPow (egraph: EGraph) =
            function
            | Name name ->
                let node = NameNode name
                // Utilise addClass' au lieu de addClass
                addClass' [node] egraph

            | Const constant ->
                let node = ConstNode constant
                addClass' [node] egraph

            | SimplifiedSum ssum ->
                let inline folderPow (acc, g0) (b, p) =
                    let id1, g1 = addSumPow g0 b
                    let id2, g2 = addSumPow g1 p
                    ((id1, id2) :: acc, g2)

                let inline folderTerm (acc, g) term =
                    let termResult, g' = List.fold folderPow ([], g) term
                    (termResult :: acc, g')

                let ids, egraph' = List.fold folderTerm ([], egraph) ssum
                let node = SumNode ids
                addClass' [node] egraph'

            | Fun (name, args) ->
                let folder (ids, g) sp =
                    let (newId, newG) = addSumPow g sp
                    (newId :: ids, newG)

                let (argIds, egraph') = List.fold folder ([], egraph) args
                let node = FunNode(name, List.rev argIds)
                addClass' [node] egraph'

        let rec public fromId (id: Id) (egraph: EGraph) =
            let eclass = findClass id egraph

            match Set.minElement eclass.nodes with
            | NameNode name -> Name name
            | ConstNode constant -> Const constant
            | SumNode ssum ->
                List.map (List.map (fun (id1, id2) -> fromId id1 egraph, fromId id2 egraph)) ssum
                |> simplifiedSumToSum
            | FunNode (name, args) -> Fun(name, List.map (flip fromId egraph) args)

        type public Rule = EGraph -> Id -> (Id * EGraph) option

        let public saturate (rules: Rule list) (egraph: EGraph) =
            let rec apply (egraph: EGraph) =
                let mutable changed = false
                let mutable egraph' = egraph

                for classId in Map.keys egraph.classes do
                    for rule in rules do
                        Option.iter (fun (newId, g) ->
                            changed <- true
                            egraph' <- merge classId newId g) (rule egraph' classId) 

                if changed then apply egraph' else egraph'

            apply egraph

        type public CostFunction = ENode -> int

        let rec public defaultCost =
            function
            | ConstNode _ -> 1
            | NameNode _ -> 1
            | SumNode ssum -> 1 + List.sumBy List.length ssum
            | FunNode (_, args) -> 1 + List.length args

        let rec public extractClass (egraph: EGraph) (costFn: CostFunction option) (classId: Id) =
            let extract = extractClass egraph costFn
            let costFn = Option.defaultValue defaultCost costFn
            let eclass = Map.find classId egraph.classes

            eclass.nodes
            |> Set.toArray
            |> Array.minBy costFn
            |> function
               | NameNode name -> Name name
               | ConstNode constant -> Const constant
               | SumNode ssum ->
                    ssum
                    |> (List.map (List.map (fun (b, p) -> extract b, extract p)))
                    |> simplifiedSumToSum
               | FunNode (name, args) -> Fun(name, List.map extract args)

        let public extract (egraph: EGraph) (rootId: Id) =
            extractClass egraph None rootId

        //  rule:  "Cos[$1]**2 + Sin[$1]**2 -> 1"

        module public Test =

            let zeroNeutralRule (egraph: EGraph) (classId: Id) =
                let eclass = findClass classId egraph

                match Set.toList eclass.nodes with
                | SumNode terms :: _ ->
                    // Look for terms that contain only a constant 0
                    let hasZeroTerm = 
                        terms |> List.exists (fun term ->
                            match term with
                            | [(id1, id2)] ->
                                let class1 = findClass id1 egraph
                                let class2 = findClass id2 egraph
                                match (Set.minElement class1.nodes, Set.minElement class2.nodes) with
                                | ConstNode (Constant 0.), ConstNode (Constant 1.) -> true
                                | _ -> false
                            | _ -> false)

                    if hasZeroTerm then
                        // Remove the zero term and return the simplified sum
                        let nonZeroTerms = 
                            terms |> List.filter (fun term ->
                                match term with
                                | [(id1, id2)] ->
                                    let class1 = findClass id1 egraph
                                    let class2 = findClass id2 egraph
                                    match (Set.minElement class1.nodes, Set.minElement class2.nodes) with
                                    | ConstNode (Constant 0.), ConstNode (Constant 1.) -> false
                                    | _ -> true
                                | _ -> true)

                        match nonZeroTerms with
                        | [] -> 
                            // If all terms were zero, return just 0
                            let (zeroId, newGraph) = addSumPow egraph (Const (Constant 0.))
                            Some(zeroId, newGraph)
                        | terms ->
                            let node = SumNode terms
                            let newGraph = addClass [node] egraph
                            Some(newGraph.nextId - 1, newGraph)
                    else
                        None
                | _ -> None

            // Active patterns pour décomposer les noeuds
            let (|IsZero|_|) (egraph: EGraph) (id: Id) =
                let eclass = findClass id egraph
                match Set.minElement eclass.nodes with
                | ConstNode (Constant 0.) -> Some()
                | _ -> None

            let (|IsOne|_|) (egraph: EGraph) (id: Id) =
                let eclass = findClass id egraph
                match Set.minElement eclass.nodes with
                | ConstNode (Constant 1.) -> Some()
                | _ -> None

            // Active pattern pour les termes zéro
            let (|IsZeroTerm|_|) (egraph: EGraph) (term: (Id * Id) list) =
                match term with
                | [(b, p)] when (match (b, p) with 
                                | IsZero egraph _, IsOne egraph _ -> true 
                                | _ -> false) -> Some()
                | _ -> None

            // Fonctions auxiliaires pour la construction
            let makeConstant (c: Constant) (egraph: EGraph) =
                let node = ConstNode c
                let egraph' = addClass [node] egraph
                (egraph'.nextId - 1, egraph')

            let makeSum (terms: (Id * Id) list list) (egraph: EGraph) =
                let node = SumNode terms
                let egraph' = addClass [node] egraph
                (egraph'.nextId - 1, egraph')


            let (|IsCos|_|) (egraph: EGraph) (id: Id) =
                let eclass = findClass id egraph
                match Set.minElement eclass.nodes with
                | FunNode ("Cos", [x]) -> Some(x)
                | _ -> None

            let (|IsSin|_|) (egraph: EGraph) (id: Id) =
                let eclass = findClass id egraph
                match Set.minElement eclass.nodes with
                | FunNode ("Sin", [x]) -> Some(x)
                | _ -> None

            let (|IsTwo|_|) (egraph: EGraph) (id: Id) =
                let eclass = findClass id egraph
                match Set.minElement eclass.nodes with
                | ConstNode (Constant 2.) -> Some()
                | _ -> None

            let (|IsSquare|_|) (egraph: EGraph) (term: (Id * Id) list) =
                match term with
                | [(base_, exp)] ->
                    match exp with
                    | IsTwo egraph _ -> Some(base_)
                    | _ -> None
                | _ -> None

            let ``Cos²[x] + Sin²[x] = 1`` (egraph: EGraph) (classId: Id) =
                let eclass = findClass classId egraph
                
                match Set.toList eclass.nodes with
                | SumNode terms :: _ ->
                    // On cherche les termes sin² et cos² dans toute la liste
                    let cosSquareAndArg = 
                        terms |> List.tryPick (function
                            | IsSquare egraph (IsCos egraph x) -> Some x
                            | _ -> None)
                            
                    let sinSquareAndArg = 
                        terms |> List.tryPick (function
                            | IsSquare egraph (IsSin egraph x) -> Some x
                            | _ -> None)
                    
                    match cosSquareAndArg, sinSquareAndArg with
                    | Some x1, Some x2 when x1 = x2 ->
                        // On a trouvé sin² x et cos² x
                        makeConstant (Constant 1) egraph |> Some  // Il faut aussi considérer le reste de la liste.
                    | _ -> None
                | _ -> None



        let public runBasic (sp: SumPow) =
            let rules: Rule list = [ Test.zeroNeutralRule; Test.``Cos²[x] + Sin²[x] = 1`` ]

            let (rootId, egraph) = addSumPow emptyEGraph sp
            let saturated = saturate rules egraph

            extract saturated rootId

    /// A module containing miscellaneous SumPow functions.
    [<RequireQualifiedAccess>]
    module public Misc =
        open PureConstantExpression
        open ElementaryOperations
        open SimplifiedSum

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
            | InternalFunction.Root _ -> true
            | _ -> false

        /// Check whether the given expression is the `fname` function.
        let public isFun (fname: string) =
            function
            | Fun(fname', _) -> fname = fname'
            | _ -> false

        let public isName (name: string) =
            function
            | Name name' -> name = name'
            | _ -> false

        /// Convert the product representation into SumPow.
        let public prodToSumPow (prod: (SumPow * SumPow) list) =
            List.map power' prod |> Term |> sumId

        /// Check whether the given expression is a sum (can contain a single element.).
        let public isSum =
            function
            | Sum xs -> List.length xs > 1
            | _ -> false

        /// Lists the syntactic variables present in the given expression (i.e. all `Name _`).
        let public listVariables (expr: SumPow) =

            let rec inner (result: string Set) =
                function
                | Name name -> Set.add name result
                | Fun(_, args) -> List.fold inner result args
                | SimplifiedSum xs ->
                    let go (b, p) = Set.union (inner result b) (inner result p)
                    mapPowFlatten go xs |> Set.unionMany
                | _ -> result

            inner Set.empty expr |> Set.toList

        /// Recursively transforms each `Root[x, nth]` of the given expression into `x^(1/nth)`.
        let rec public convertAllRootsToPower =
            function
            | InternalFunction.Root(x, PureConstantExpressionInteger nth) -> (convertAllRootsToPower x) ** (1 / Const nth)
            | Power(b, p) -> convertAllRootsToPower b ** convertAllRootsToPower p
            | Fun(fname, args) -> Fun(fname, List.map convertAllRootsToPower args)
            | SumList xs -> Sum (manyTermId (List.map convertAllRootsToPower xs))
            | other -> other

        /// Recursively transforms each `x^(1/nth)` of the given expression into `Root[x, nth]`.
        let rec public convertAllRationalPowersToRoot =
            function
            | Power(b, PureConstantExpressionRational(num, den)) -> Fun("Root", [ b ** num; Const den ])
            | InternalFunction.Root(x, PureConstantExpressionInteger nth) -> Fun("Root", [ x; Const nth ])
            | Power(b, p) -> convertAllRationalPowersToRoot b ** convertAllRationalPowersToRoot p
            | Fun(fname, args) -> Fun(fname, List.map convertAllRationalPowersToRoot args)
            | SumList xs -> Sum (manyTermId (List.map convertAllRationalPowersToRoot xs))
            | other -> other

