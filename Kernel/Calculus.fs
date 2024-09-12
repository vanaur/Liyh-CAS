namespace Liyh.Kernel

#nowarn "3391"

//    Implements methods for univariate and multivariate calculus
//        - Sum and series
//        - Limits
//        - Derivatives
//        - Primitives
//        - Integrals

module rec Calculus =
    open Liyh.Utils
    open Liyh.Kernel
    open Liyh.Kernel.TrueVariable
    open SumPow.InternalFunction

    exception public UnknownFunctionException of string
    exception public UnknownExpressionException of SumPow

    /// Checks whether the given expression contains `Name variable`.
    let inline private containsVariable (variable: string) (expr: SumPow) =
        containsVariables expr [ variable ]


    module public Derive =

        /// Returns the univariate derivative of the expression given in the indicated variable.
        let rec public sderive (variable: string) =
            function
            | Const _ -> Const Zero
            | sp when not (containsVariable variable sp) -> Const Zero
            | Name name when name = variable -> Const One
            | Sum xs -> sderiveSum variable xs
            | InternalFunction ifun -> sderiveInternalFunction variable ifun
            | Fun(fn, _) -> raise (UnknownFunctionException fn)
            | other -> raise (UnknownExpressionException other)

            >> Simplification.expandAndSimplify // faudra mieux faire

        and private sderiveSum (variable: string) (sum: Term list) =
            Sum (List.collect (function Term term -> sderiveTerm variable term) sum)

        and private sderiveTerm (variable: string) (term: Pow list) =
            List.fold (fun acc a -> Term (sderivePow variable a :: List.remove (( = ) a) term) :: acc) [] term

        and private sderivePow (variable: string) =
            function
            | Pow(Name name, sp) when name = variable && not (containsVariable variable sp) ->
                powId (sp * (Name name ** (sp - 1)))

            | Pow(sp, Name name) when name = variable && not (containsVariable variable sp) ->
                powId (liyhLn sp * (sp ** Name name))

            | Pow(f, g) ->
                powId ((f ** (g - 1)) * (g * sderive variable f + f * liyhLn f * sderive variable g))

        and private sderiveInternalFunction (variable: string) =
            function
            | LiyhAbs x -> sderive variable x * liyhSgn x
            | LiyhArCos x -> sderive variable x * (-1 / liyhSqrt (1 - x ** 2))
            | LiyhArCosh x -> sderive variable x * (1 / (liyhSqrt (x - 1) * liyhSqrt (x + 1)))
            | LiyhArCot x -> sderive variable x * (-1 / (x ** 2 + 1))
            | LiyhArCoth x -> sderive variable x * (1 / (1 - x ** 2))
            | LiyhArCsc x -> sderive variable x * (-1 / (liyhSqrt (1 - 1 / (x ** 2)) * (x ** 2)))
            | LiyhArCsch x -> sderive variable x * (-1 / (liyhSqrt (1 / (x ** 2) + 1) * (x ** 2)))
            | LiyhArSec x -> sderive variable x * (1 / (liyhSqrt (1 - 1 / (x ** 2)) * (x ** 2)))
            | LiyhArSech x -> sderive variable x * (-1 / (liyhSqrt (1 / x - 1) * liyhSqrt (1 / x + 1) * (x ** 2)))
            | LiyhArSin x -> sderive variable x * (1 / liyhSqrt (1 - x ** 2))
            | LiyhArSinh x -> sderive variable x * (1 / liyhSqrt (x ** 2 + 1))
            | LiyhArTan x -> sderive variable x * (1 / (x ** 2 + 1))
            | LiyhArTanh x -> sderive variable x * (1 / (1 - x ** 2))
            | LiyhCos x -> sderive variable x * -liyhSin x
            | LiyhCosh x -> sderive variable x * liyhSinh x
            | LiyhCot x -> sderive variable x * -(liyhCsc x ** 2)
            | LiyhCoth x -> -(liyhCsch x) ** 2
            | LiyhCsc x -> sderive variable x * -liyhCot x * liyhCsc x
            | LiyhCsch x -> sderive variable x * -liyhCoth x * liyhCsch x
            | LiyhExp x -> sderive variable x * liyhExp x
            | LiyhLog(x, None) -> sderive variable x * (1 / x)
            | LiyhLog(x, Some b) -> sderive variable x * (1 / (x * liyhLn b))
            | LiyhPow(b, p) -> sderive variable (b ** p)
            | LiyhRoot(x, None) -> sderive variable x * (1 / (2 * liyhSqrt x))
            | LiyhRoot(x, Some nth) -> sderive variable x * sderive variable (x ** 1 / nth)
            | LiyhSec x -> sderive variable x * liyhTan x * liyhSec x
            | LiyhSech x -> sderive variable x * -liyhTanh x * liyhSech x
            | LiyhSin x -> sderive variable x * liyhCos x
            | LiyhSinh x -> sderive variable x * liyhCosh x
            | LiyhTan x -> sderive variable x * (liyhSec x) ** 2
            | LiyhTanh x -> sderive variable x * (liyhSech x) ** 2
            | LiyhSgn x -> sderive variable x * 2 * liyhDelta x
            | LiyhCeil x -> failwith "TODO: need Context.fs"
            | LiyhDelta x -> failwith "TODO: need Context.fs"
            | LiyhFloor x -> failwith "TODO: need Context.fs"
            | LiyhRound x -> failwith "TODO: need Context.fs"
            | LiyhSinc x -> failwith "TODO: need Context.fs"
            | LiyhId x -> sderive variable x

        /// Returns the univariate nth-derivative of the expression given in the indicated variable.
        let public sNthDerive (variable: string) (nth: int) (expr: SumPow) =

            let rec loop result =
                function
                | n when n < 0 -> invalidArg "nth" "negative nth-derivative."
                | 0 -> result
                | n -> loop (sderive variable result) (n - 1)

            (memoize loop) expr nth

    module public NumericEvaluation =
        open SumPow.NumericEvaluation

        module public Integration =

            /// Lists the different numerical integration methods based on interpolation.
            /// See https://en.wikipedia.org/wiki/Numerical_integration#Quadrature_rules_based_on_interpolating_functions.
            [<Struct; RequireQualifiedAccess>]
            type public ByInterpolationMethod =
                | Left = 0
                | Right = 1
                | Midpoint = 2
                | Trapezoid = 3
                | Simpson = 4

            // The lambda in order of the different integration by interpolation methods.
            let private byInterpolationMethods =
                [| fun f dx x -> f x
                   fun f dx x -> f (x + dx)
                   fun f dx x -> f (x + dx / 2.)
                   fun f dx x -> (f x + f (x + dx)) / 2.
                   fun f dx x -> (f x + 4. * f (x + dx / 2.) + f (x + dx)) / 6. |]

            /// Numerically integrates the given univariate expression in the given variable in the interval `[a, b]`
            /// and with a maximum number of iterations `steps`.
            let public integrateByInterpolation (method: ByInterpolationMethod) (a: double) (b: double) (steps: int) (expr: SumPow) (variable: string) =
                let dx = (b - a) / double steps
                let method = byInterpolationMethods.[int method] (makef1 expr variable) dx

                let rec loop k s =
                    if k >= steps then s
                    else loop (k + 1) (s + method (a + dx * double k))

                dx * loop 0 0.

            /// Implements Gauss quadrature for the numerical integration of the given expression in the interval `[a, b]`
            /// with a specified tollérence and a given maximum number of iterations. This is the default algorithm used.
            let public gaussianQuadrature (a: double) (b: double) (steps: int) (eps: double) (expr: SumPow) (variable: string) =

                // Function to evaluate the Legendre n-polynomial in x.
                let inline legendre (n: int) (x: double) =
                    let rec loop n p0 p1 x =
                        if n = 0 then p0
                        elif n = 1 then p1
                        else loop (n - 1) p1 (((2.0 * double n - 1.0) * x * p1 - (double n - 1.0) * p0) / double n) x
                    loop n 1.0 x x

                // Derivative of the Legendre n-polynomial.
                let inline legendreDeriv (n: int) (x: double) =
                    (double n * (x * legendre n x - legendre (n - 1) x)) / (x * x - 1.0)

                // Newton's method for finding the roots of Legendre's polynomial.
                let inline newtonLegendre (n: int) (guess: double) =
                    let rec loop x =
                        let fx = legendre n x
                        if abs fx < eps then x
                        else
                            let fpx = legendreDeriv n x
                            loop (x - fx / fpx)
                    loop guess

                // Calculation of points and weights for Gauss quadrature.
                let inline gaussLegendre (n: int) =
                    let points = Array.init n (fun i ->
                        let guess = cos (System.Math.PI * (double (i + 1) - 0.25) / (double n + 0.5))
                        newtonLegendre n guess)
                    
                    let weights = Array.init n (fun i ->
                        let x = points.[i]
                        2.0 / ((1.0 - x * x) * (legendreDeriv n x) ** 2.0))
                    
                    points, weights

                let f = makef1 expr variable
                let points, weights = gaussLegendre steps
                let midpoint = (b + a) / 2.0
                let halfLength = (b - a) / 2.0

                Array.fold2 (fun acc x w -> acc + w * f (midpoint + halfLength * x)) 0.0 points weights * halfLength

