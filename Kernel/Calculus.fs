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

