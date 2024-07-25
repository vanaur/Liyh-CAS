namespace Liyh.Kernel.LinearAlgebra

[<AutoOpen>]
module LinearAlgebra =
    open Liyh.Kernel.LinearAlgebra.Vector
    open Liyh.Kernel.LinearAlgebra.Matrix
    open Liyh.Kernel.LinearAlgebra.Tensor
    open Liyh.Kernel.SumProd

    /// Check wether the vectors are linearly independent.
    let public areVectorsLinearlyIndependent (vectors: Vector seq) =
        //
        //    let mat = Matrix.FromVectors vectors
        //    simp mat.Determinant <> Zero
        //
        // ^bah SumProd (SIMP) il marche pas

        // Much more performant solution:
        //
        //    let zero = Matrix.Create((Seq.item 0 vectors).Length, 1, fun _ _ -> Zero)
        //    Matrix.Solve(Matrix.FromVectors vectors ++ zero) |> Option.isSome
        //
        // but only for floats :(

        let zero = Matrix.Create((Seq.item 0 vectors).Length, 1, fun _ _ -> Zero)
        Matrix.Solve(Matrix.FromVectors vectors ++ zero) |> Option.isSome

    let public areMatricesLinearlyIndependent (matrices: Matrix seq) =
        0
