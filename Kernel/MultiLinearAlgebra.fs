namespace Liyh.Kernel

#nowarn "3391"
#nowarn "25"

/// This module covers vector, matrix and tensor algebra.
module public rec MultiLinearAlgebra =
    open System
    open Liyh.Kernel
    open Liyh.Utils

    /// This module deals with naive vector algebra over SumPow.
    module public Vector =
        exception public VectorsHaveDifferentLengthException of Vector seq
        exception public VectorHasNoComponentException
        exception public CrossProductOfNon3VectorsException of Vector * Vector

        [<Symbolic; CustomComparison; CustomEquality>]
        type public Vector =
            | Vector of SumPow[]

            member this.Item
                with get (index: int) =
                    let (Vector components) = this
                    components.[index]

            // -- Implement interfaces -- //

            interface IComparable with
                member v1.CompareTo obj =
                    match obj with
                    | :? Vector as (Vector cs2) ->
                        let cs1 = components v1
                        compare cs1 cs2

                    | _ -> invalidArg "obj" "cannot compare value of different types"

            interface ISymbolic with
                member this.ToSymbolic() = toSymbolic this
                member this.ToLatex() = Some(toLatex this)
                member this.ToLatexOrString() = toLatex this
                member this.Hash = hash this

            override this.GetHashCode() = hashVector this
            override this.Equals arg = equalsVector this arg

            static member op_Addition(a: Vector, b: Vector) = Operations.addition a b
            static member op_Subtraction(a: Vector, b: Vector) = Operations.subtraction a b
            static member op_Multiply(scalar: SumPow, v: Vector) = Operations.scalarMultiplication scalar v
            static member op_Division(v: Vector, scalar: SumPow) = Operations.scalarDivision v scalar
            static member op_UnaryNegation(v: Vector) = Const -1 * v

        /// The null vector of dimension `size`.
        let public zeroVector (size: int) =
            if size <= 0 then
                raise VectorHasNoComponentException
            
            Vector [| for _ = 1 to size do Const Zero |]

        let private toSymbolic (Vector components) =
            let arguments = Array.map (tuple2 null << Atomic.toSymbolic) components

            { atom = Atomic.Identifier "Vector"
              attributes = List.ofArray arguments }

        let private toLatex (Vector components) =
            let components = Array.map toLatexValue components
            sprintf @"\left(%s\right)" (System.String.Join(", ", components))

        let private hashVector (Vector components) =
            HashCode.Combine(Vector, components)

        let private equalsVector (Vector cs1) (v2: obj) =
            match v2 with
            | :? Vector as (Vector cs2) -> cs1 = cs2
            | _ -> false

        /// Returns the components of the vector.
        let public components (Vector components) =
            if Array.isEmpty components then
                raise VectorHasNoComponentException

            components

        /// Create a vector from the given components.
        let public fromSeq (components: SumPow seq) =
            if Seq.isEmpty components then
                raise VectorHasNoComponentException

            Vector (Array.ofSeq components)

        module private Operations =

            let public addition (v1: Vector) (v2: Vector) =
                let cs1 = components v1
                let cs2 = components v2

                if Array.length cs1 <> Array.length cs2 then
                    raise (VectorsHaveDifferentLengthException [ v1; v2 ])

                Vector (Array.map2 ( + ) cs1 cs2) |> simplifyComponents

            let public subtraction (v1: Vector) (v2: Vector) =
                let cs1 = components v1
                let cs2 = components v2

                if Array.length cs1 <> Array.length cs2 then
                    raise (VectorsHaveDifferentLengthException [ v1; v2 ])

                Vector (Array.map2 ( - ) cs1 cs2) |> simplifyComponents
            
            /// Multiply each component of the given vector by the given scalar.
            let public scalarMultiplication (scalar: SumPow) (Vector components) =
                if Misc.isZero scalar
                then Vector (Array.init (Array.length components) (konst (Const Zero)))
                else
                    if Misc.isOne scalar
                    then Vector components
                    else Vector (Array.map (( * ) scalar) components) |> simplifyComponents

            /// Divise each component of the given vector by the given scalar.
            let public scalarDivision (Vector components) (scalar: SumPow) =
                if Misc.isZero scalar
                then Vector (Array.init (Array.length components) (konst (Const Zero)))
                else
                    if Misc.isOne scalar
                    then Vector components
                    else Vector (Array.map (fun c -> c / scalar) components) |> simplifyComponents

        /// Returns the sum of the component-by-component product of the two given vectors of the same size.
        let public dotProduct (v1: Vector) (v2: Vector) =
            let cs1 = components v1
            let cs2 = components v2

            if Array.length cs1 <> Array.length cs2 then
                raise (VectorsHaveDifferentLengthException [ v1; v2 ])

            Array.fold2 (fun acc a b -> acc + (a * b)) (Const Zero) cs1 cs2

        let private size (Vector components) =
            Array.length components

        let private simplifyComponents (Vector components) =
            Vector(Array.map Simplification.simplifyAndExpand components)

        /// Check whether the vector has norm 1.
        let public isUnitVector (v: Vector) =
            enorm v = Const One

        /// Calculate the Euclidean norm of the given vector.
        let public enorm (Vector components) =
            let arg = Array.fold (fun acc c -> acc + (c ** 2)) (Const Zero) components
            Fun("Sqrt", [ arg ]) |> Simplification.simplify

        /// Returns the angle formed by the two vectors.
        let public angle (v1: Vector) (v2: Vector) =
            let cs1 = components v1
            let cs2 = components v2

            if Array.length cs1 <> Array.length cs2 then
                raise (VectorsHaveDifferentLengthException [ v1; v2 ])

            let arg = dotProduct v1 v2 / (enorm v1 * enorm v2)
            Fun("Cos", [ arg ]) |> Simplification.simplify

        /// Project the vector `v1` onto the vector `v2`.
        /// See https://en.wikipedia.org/wiki/Vector_projection.
        let public project (v1: Vector) (v2: Vector) =
            let cs1 = components v1
            let cs2 = components v2

            if Array.length cs1 <> Array.length cs2 then
                raise (VectorsHaveDifferentLengthException [ v1; v2 ])

            let num = dotProduct v2 v1
            let den = dotProduct v1 v1

            Operations.scalarMultiplication (num / den) v1
            |> simplifyComponents

        /// Returns the cross-product of the two given vectors.
        /// See https://en.wikipedia.org/wiki/Cross_product.
        let public crossProduct (v1: Vector) (v2: Vector) =
            let cs1 = components v1
            let cs2 = components v2

            if Array.length cs1 <> 3 || Array.length cs2 <> 3 then
                raise (CrossProductOfNon3VectorsException (v1, v2))

            let [| a1; a2; a3 |] = cs1
            let [| b1; b2; b3 |] = cs2

            Vector [| (a2 * b3 - a3 * b2); (a3 * b1 - a1 * b3); (a1 * b2 - a2 * b1) |]

        /// Returns the vector connecting the two given points.
        let public joinPoints (point1: SumPow[]) (point2: SumPow[]) =
            if Array.length point1 <> Array.length point2 then
                raise (VectorsHaveDifferentLengthException [ Vector point1; Vector point2 ])

            if Array.isEmpty point1 then
                raise VectorHasNoComponentException

            Vector(Array.map2 ( - ) point1 point2)

        /// Normalize the given vector by its enorm.
        let public normalize (v: Vector) =
            match enorm v with
            | Zero -> raise (DivideByZeroException(sprintf "%A" v))
            | m -> v / m

        /// Generates a set of mutually orthogonal vectors given a base set.
        /// See https://en.wikipedia.org/wiki/Gram%E2%80%93Schmidt_process.
        let public gramSchmidt (vectors: Vector array) =
            if not (Array.forall (fun v -> size v = size vectors.[0]) vectors) then
                raise (VectorsHaveDifferentLengthException vectors)

            let mutable result = Array.copy vectors

            for k = 0 to Array.length vectors - 1 do
                for j = 0 to k - 1 do
                    result.[k] <- result.[k] - project result.[j] vectors.[k]

            result

        /// Generates a set of normalized mutually orthogonal vectors given a base set.
        /// See https://en.wikipedia.org/wiki/Gram%E2%80%93Schmidt_process.
        let public gramSchmidtNormalized (vectors: Vector array) =
            Array.map (fun v -> simplifyComponents (v / enorm v)) (gramSchmidt vectors)

        let public areLinearlyDependent (vectors: Vector array) =
            false

    module public Matrix =

        [<Symbolic>]
        type public Matrix = SumPow[,]

    module public Tensor =

        type public Tensor =
            { indices: TensorIndex list
              dimension: int
              components: SumPow[] option }
        
        and public TensorIndex = Variance * string

        and public Variance =
        | Covariant
        | Contravariant
