namespace Liyh.Kernel.LinearAlgebra

module rec Tensor =
    open System.Collections.Generic
    open Liyh.Kernel.LinearAlgebra.Vector
    open Liyh.Kernel.LinearAlgebra.Matrix
    open Liyh.Kernel.SumProd

    /// Liyh follows Einstein's summation convention, so tensors in their index form are represented by,
    /// among other things, indices and index gymnastics.
    type public TensorIndex =
        | UpperIndex of string
        | LowerIndex of string

    /// Gets the variance of the tensor in the form (covariant, contravariant).
    let private variance indices =

        let inner acc = function
            | LowerIndex _ -> (fst acc + 1, snd acc)
            | _ -> (fst acc, snd acc + 1)
        
        Seq.fold inner (0, 0) indices

    /// The basic ranking of tensors is implemented.
    let private ranking dimension rank (position: int list) =
        assert (position.Length = rank)

        let inner acc i = let p = pown dimension (rank - i) in acc + position.[i - 1] * p
        Array.fold inner 0 [| 1 .. rank |]

    /// Represents a SumProd tensor in the sense of tensorial algebra and provides the standard operations.
    type public Tensor(indices: TensorIndex list, dimension: int) =
        let components = List<SumProd>()
        let rank = indices.Length

        /// Gets the rank of the tensor.
        member __.Rank = rank

        /// Gets the variance of the tensor in the form (covariant, contravariant).
        member __.Variance = variance indices

        /// Gets the tensor component at the specified tensor position, assuming the indices start at 0.
        /// The given list represents the position (i, ..., d).
        member __.Item
            with get (position: int list) =
                let pos = ranking dimension rank position
                components.[pos]

        /// Sets the tensor component at the specified tensor position, assuming the indices start at 0.
        /// The given list represents the position (i, ..., d).
        member __.Set
            with set (position: int list) (value: SumProd) =
                let pos = ranking dimension rank position
                components.[pos] <- value

        /// Define the values of the tensor.
        member __.FillComponents (values: SumProd seq) =
            components.AddRange values

// Définir les opérations basiques, et aussi est-ce que `List` est judicieux ?

