namespace Liyh.Kernel

#nowarn "3391"
#nowarn "25"
#nowarn "46"

/// This module deals with classical tensor algebra over SumPow and index notation.
module public rec Tensor =
    open Liyh.Kernel.LinearAlgebra
    open Liyh.Utils
    open Index

    //
    // Note: the tensors we are referring to here, in Liyh and this module especially, are those which meet
    // the definition of multi-linear mapping and not a data structure commonly encountered in machine learning
    // which consists, roughly speaking, of a multi-dimensional array. Although there are overlaps, Liyh tensors
    // are not simply generalized m-dimensional matrices, or at least that's not how Liyh's tensors are designed.
    //
    // Many of the concepts discussed here are based on Ricci's calculus, with physical applications in mind.
    // See https://en.wikipedia.org/wiki/Ricci_calculus.
    //

    module public Abstract =

        [<Struct>]
        type public TensorProperty =
            | IsSymmetric of indices: string list option    // The object is symmetrical in the given indices
            | IsAntisymmetric of string list option         // The object is antisymmetric in the given indices
            | IsPseudoTensor                                // The object does not transform exactly like a tensor

            | IsPartialDerivative                           // The object behaves as a partial derivative
            | IsCovariantDerivative                         // The object behaves as a covariant derivative
            | IsConnection                                  // The object behaves as a connection

            | IsKroneckerDelta                              // The object is the Kronecker delta
            | IsLeviCivita                                  // The object is the Levi-Civita symbol
            | IsMetric                                      // The object is a metric

        type public AbstractTensor =    
            { name: string                       // The name of the tensorial symbol
              indices: IndexContext              // The indices attached to it
              properties: TensorProperty list }  // Some properties of the tensorial symbol

        type public AbstractTensorExpression =
            { expression: AbstractTensor list   // Each individual context
              context: IndexContext }           // General context

        let public toAbstractTensor =
            function
            | Fun("IndexedTensor", Name name :: Fun("Indices", args) :: []) ->

                let toTensorIndex =
                    function
                    | Fun(variance, [ Name name ]) ->
                        { attachedTo = name
                          possibleValues = None
                          variance = if variance = "CovariantIndex" then Covariant else Contravariant
                          usage = FreeIndex  // Si on a une expression de tenseurs, comment déterminer ceux qui sont dummy
                                             // et ceux qui sont summed ? Parce que à part si le tenseur self-contract, on
                                             // ne peut à priori pas savoir...
                          notation = getBuiltinNotationFromName name    
                          name = name }
                    | _ -> failwith "??"

                { name = name
                  indices = { context = List.map toTensorIndex args }
                  properties = [] }

            | _ -> failwith "??"

        let public toLatexAbstractTensor { name = name; indices = { context = ctx } } =
            sprintf @"%s%s" name (System.String.Join("", List.map toLatexIndex ctx))

        let public toLatexAbstractTensorExpression { expression = expression } =
            System.String.Join(' ', List.map toLatexAbstractTensor expression)

        /// Rename the indices of the tensor given by the map.
        let inline private renameIndices (map: Map<string, string>) (tensor: AbstractTensor) =

            let inline inner (index: Index) =
                Map.tryFind index.name map
                |> Option.map (fun newName -> { index with name = newName })
                |> Option.defaultValue index

            { tensor with indices = { context = List.map inner tensor.indices.context } }

        /// Check the consistency of tensor indices according to Einstein's convention.
        let public isTensorConsistent (t: AbstractTensor) =
            isIndexConsistent t.indices
            && List.forall (_.attachedTo >> ( = ) t.name) t.indices.context

        /// Check whether the "pseudo-tenor" property has been associated with the given tensor.
        /// See https://en.wikipedia.org/wiki/Pseudotensor.
        let public isPseudoTensor { properties = properties } =
            List.contains IsPseudoTensor properties

        /// Check whether the "KroneckerDelta" property has been associated with the given tensor.
        /// See https://en.wikipedia.org/wiki/Kronecker_delta.
        let public isKroneckerDelta { properties = properties } =
            List.contains IsKroneckerDelta properties

        /// Check whether the "LeviCivita" property has been associated with the given tensor.
        /// See https://en.wikipedia.org/wiki/Levi-Civita_symbol.
        let public isLeviCivitaSymbol { properties = properties } =
            List.contains IsLeviCivita properties

        /// Check whether the "Metric" property has been associated with the given tensor.
        /// See https://en.wikipedia.org/wiki/Metric_tensor.
        let public isMetric { properties = properties } =
            List.contains IsLeviCivita properties

        /// Returns the rank of the given tensor (taking into account self-contractions).
        let public tensorRank { indices = { context = ctx } } =
            List.length ctx - 2 * List.length (getContractedIndices { context = ctx })

        /// Returns tensor type `(n, m)` where `n` is the number of contravariant indices and `m` is the
        /// number of covariant ones.
        let public tensorType { indices = { context = ctx } } =
            let contravariants, covariants = List.partition (_.variance >> ( = ) Contravariant) ctx
            List.length contravariants, List.length covariants

        /// "Chain tensors components" in an expression using Einstein notation.
        /// For example, `gᵢⱼuⁱvʲ`.
        let public chain (tensors: AbstractTensor list) =
            let ctx, map = mergeMany (List.map (fun context -> context.indices) tensors)
            let tensors = List.map (renameIndices map) tensors

            { expression = tensors
              context = ctx }

        // let public simplify = ...

        let public define (tensor: AbstractTensor) (expression: AbstractTensorExpression) =
            // correspondre varince +=> Change index usage // <<--<<--<<--
            0



(*

    let private isCovariant =
        function
        | Covariant -> true
        | _ -> false
    
    let private isContravariant =
        not << isCovariant

    type private IndexContext = Set<string>

    let private initialIndexContext = Set.empty

    let inline private newIndex (icontext: IndexContext) =
        let diff = Set.difference icontext lowercaseGreekLetters
        let ni =
            if Set.isEmpty diff then
                match Seq.tryHead icontext with
                | None -> Seq.head lowercaseGreekLetters
                | Some h -> h + "'"
            else
                Seq.head diff
        ni, Set.add ni icontext

    /// Represents a tensor in a semi-abstract way, it may or may not contain explicit values
    /// and use abstract index notation.
    [<Symbolic>]
    type public Tensor =
        { indices: Index list
            dimension: int
            components: SumPow[] option }

    /// Get the order/rank of the given tensor (i.e. the number of indices).
    let inline public order { indices = indices } =
        List.length indices

    /// The tensors are classified according to their type (n, m), where n is the number of contravariant indices,
    /// m is the number of covariant indices, and n + m gives the total order of the tensor. 
    let public tensorType { indices = indices } =
        let contravariants, covariants = List.partition (fst >> isContravariant) indices
        List.length contravariants, List.length covariants

    let inline public abstractTensor (indices: Index list) (dim: int) =
        { indices = indices 
            dimension = dim
            components = None }

    let inline public filledTensor (indices: Index list) (dim: int) (components: SumPow seq) =
        { indices = indices 
            dimension = dim
            components = Some (Seq.toArray components) }

    let inline private isFilled { components = components } =
        Option.isSome components

    let inline private getIndexes { indices = indices } =
        List.map snd indices

    /// Recovers the nth-component of the tensor by ranking. If the tensor is purely abstract, then the function raise
    /// an exception. For example, for a 4-tensor, we can obtain the component located at (x₁, x₂, x₃, x₄). 
    let inline public component (tensor: Tensor) (position: int list) =
        if not (isFilled tensor) then
            raise (UnfilledTensorException tensor)

        let rk = order tensor

        if List.length position <> rk then
            raise (TensorComponentOverflowException (tensor, position))

        let position = List.rev position
        let mutable r = 0

        for j = 1 to rk do
            let p = pown tensor.dimension (rk - j)
            r <- r + position.[j - 1] * p

        let components = Option.get tensor.components

        if r > Array.length components then
            raise (TensorComponentOverflowException (tensor, position))

        components.[r]

    let public apply1KronokerDelta ((_, i1): Index) ((_, i2): Index) =
        if i1 = i2 then 1 else 0

    /// Calculation of a determinant that is not very optimised but it is sufficient for small int matrices.
    let rec private quickIntDet (matrix: int[,]) =
        let n = Array2D.length1 matrix

        if n = 1 then matrix.[0, 0]
        else
            let initializer i r c =
                if r < i then matrix.[r, c + 1]
                else matrix.[r + 1, c + 1]

            Array.sumBy (fun i ->
                let subMatrix = Array2D.init (n - 1) (n - 1) (initializer i)
                let sign = if i % 2 = 0 then 1 else -1
                sign * matrix.[i, 0] * quickIntDet subMatrix) [| 0 .. n - 1 |]

    /// Calculates the generalised Kronecker Delta given a list of index pairs.
    /// For example,
    /// 
    ///     [ (Covariant, "b"), (Covariant, "b")
    ///       (Covariant, "c"), (Covariant, "c")
    ///       (Covariant, "a"), (Covariant, "a")
    ///       (Covariant, "b"), (Covariant, "b") ]
    /// 
    /// The basic Kronecker Delta δⁱⱼ correspond to the singleton `[ (i, j) ]`.
    let public applyKronokerDelta (indices: (Index * Index) list) =
        let l = List.length indices
        Array2D.init l l (fun i j ->
            let (μᵢ, νᵢ) = indices.[i]
            let (μⱼ, νⱼ) = indices.[j]
            apply1KronokerDelta μᵢ νⱼ)
        |> quickIntDet

*)

