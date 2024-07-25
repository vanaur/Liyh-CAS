namespace Liyh.Kernel.SumPow

module public rec MultiLinearAlgebra =
    open System.Collections.Generic
    open System
    open Liyh.Kernel
    open System.Runtime.CompilerServices
    open Liyh.Kernel.Constant
    open Liyh.Utils

    module public Vector =
        exception public VectorsHaveDifferentLength of SumPow[] list

        [<Symbolic>]
        type public Vector = Vector of SumPow[] 

        let public simplifyComponents (Vector v) =
            Vector(Array.map Simplification.simplifyAndExpand v)

        let private addition (Vector v1) (Vector v2) =
            if Array.length v1 <> Array.length v2 then raise (VectorsHaveDifferentLength [ v1; v2 ])
            Vector (Array.map2 ( + ) v1 v2) |> simplifyComponents

        let private subtraction (Vector v1) (Vector v2) =
            if Array.length v1 <> Array.length v2 then raise (VectorsHaveDifferentLength [ v1; v2 ])
            Vector (Array.map2 ( - ) v1 v2) |> simplifyComponents
        
        let private scalarMultiplication (scalar: SumPow) (Vector v) =
            if Misc.isZero scalar then Vector (Array.init 0 (konst (SumPow.Const Zero))) else
            if Misc.isOne scalar then Vector v else
            Vector (Array.map (( * ) scalar) v) |> simplifyComponents
        
        let private dotProduct (Vector v1) (Vector v2) =
            if Array.length v1 <> Array.length v2 then raise (VectorsHaveDifferentLength [ v1; v2 ])
            Array.fold2 (fun acc a b -> acc + (a * b)) (SumPow.Const Zero) v1 v2

        let private norm (Vector v) =
            let arg = Array.reduce (fun acc c -> acc + c ** 2) v
            Fun("Sqrt", [ arg ])

        let private angle ((Vector v1) as a) ((Vector v2) as b) =
            if Array.length v1 <> Array.length v2 then raise (VectorsHaveDifferentLength [ v1; v2 ])

            let arg = dotProduct a b / (norm a * norm b)
            Fun("Cos", [ arg ])

        let private project ((Vector v1) as a) ((Vector v2) as b) =
            if Array.length v1 <> Array.length v2 then raise (VectorsHaveDifferentLength [ v1; v2 ])
            scalarMultiplication ((dotProduct b a) / (dotProduct a b)) a

        let private areOrthogonal ((Vector v1) as a) ((Vector v2) as b) =
            if Array.length v1 <> Array.length v2 then raise (VectorsHaveDifferentLength [ v1; v2 ])
            // ça DOIT renvoyer une équation

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
