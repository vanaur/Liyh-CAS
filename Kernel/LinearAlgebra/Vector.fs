namespace Liyh.Kernel.LinearAlgebra

module rec Vector =
    open Liyh.Kernel.SumProd

    /// A vector is either a row vector or a column vector.
    type [<Struct>] public VectorKind =
        | RowVector
        | ColumnVector

    /// Changes row vector to column vector and column vector to row vector.
    let private transpose = function
        | RowVector -> ColumnVector
        | ColumnVector -> RowVector

    /// Vector addition.
    let private addition (v1: SumProd[]) (v2: SumProd[]) =
        assert (v1.Length = v2.Length)
        Array.map2 ( + ) v1 v2

    /// Multiply a vector by a scalar.
    let private scalarMultiplication (v: SumProd[]) (scalar: SumProd) =
        if isZero scalar  then Array.create v.Length Zero
        elif isOne scalar then v
        else Array.map (( * ) scalar) v

    /// Dot product of two vectors.
    let private dotProduct' (v1: SumProd[]) (v2: SumProd[]) =
        Array.fold2 (fun acc a b -> acc + (a * b)) Zero v1 v2

    /// Projects a vector onto another vector.
    let private project' (baseV: SumProd[]) (v: SumProd[]) =
        scalarMultiplication baseV ((dotProduct' v baseV) / (dotProduct' baseV baseV))

    /// Get the magnitude of the given vector.
    let private norm (v: SumProd[]) =
        Function("Sqrt", [dotProduct' v v])

    /// Normalize the given vector.
    let private normalize (v: SumProd[]) =
        assert (not (Array.isEmpty v))        
        scalarMultiplication v (Integer 1I / norm v)

    /// Factorise the given vector.
    let private factorize (v: SumProd[]) =
        let ggcd = GSPGCD v
        ggcd, Array.map (fun a -> a / ggcd) v // marche pas trop pour les fractions (correct mais allourdi)

    /// Represents a SumProd vector in the sense of linear algebra and provides the standard operations.
    type public Vector(length: int, kind: VectorKind option, content: SumProd[] option) =

        /// By default, an unspecified kind of vector is a line vector.
        let kind = if kind.IsNone then RowVector else kind.Value

        /// The content of a matrix is encoded as a two-dimensional array using `array`.
        let content =
            match content with
            | None -> Array.create length Undefined
            | Some xs -> assert (length = xs.Length); xs

        new (length: int, content: SumProd[] option) = Vector(length, None, content)
        new (length: int) = Vector(length, None)
        new (content: SumProd[]) = Vector(content.Length, Some content)
        new (content: bigint[]) = Vector(Array.map Integer content)
        new (content: float[]) = Vector(Array.map Float content)

        override __.ToString () =
            sprintf "%A" content

        member public __.ToLatex =
            let tmp = 
                match kind with
                | RowVector -> [| for x in content -> x.ToLatex |]
                | ColumnVector ->
                    let s = System.String.Join(@"\\", [| for x in content -> x.ToLatex |])
                    [| sprintf @"\begin{align}%s\end{align}" s |]

            sprintf @"\left[%s\right]" (System.String.Join(",", tmp))

        member public __.Item
            with get(i) = content.[i]

        /// Returns the Array content of the vector.
        member public __.Content = content

        member public __.Transpose = Vector(length, Some (transpose kind), Some content)
        member public __.Length = length
        member public __.Kind = kind
        member public __.IsRowVector = match kind with RowVector -> true | _ -> false
        member public __.IsColVector = match kind with ColumnVector -> true | _ -> false
        member public __.Normalized = Vector(normalize content)
        member public __.Norm = norm content
        member public __.Factorize = let c, v = factorize content in c, Vector v

        member public __.Map (mapper: SumProd -> SumProd) = Vector(Array.map mapper content)
        member public __.Map (mapper: SumProd -> bigint) = Vector(Array.map mapper content)
        member public __.Map (mapper: SumProd -> float) = Vector(Array.map mapper content)

        static member public ( + ) (v1: Vector, v2: Vector) = Vector(addition v1.Content v2.Content)
        static member public ( - ) (v1: Vector, v2: Vector) = v1 + v2.Map neg
        static member public ( * ) (a: SumProd, v: Vector) = scalarMultiplication v.Content a
        static member public ( * ) (v: Vector, a: SumProd) = a * v

        /// Dot product of same-length vectors.
        static member public DotProduct (v1: Vector, v2: Vector) =
            assert (v1.Length = v2.Length)
            dotProduct' v1.Content v2.Content

        /// Projects a the vector v1 onto the vector v2.
        static member public Project (v1: Vector, v2: Vector) =
            assert (v1.Kind = v2.Kind)
            Vector(project' v1.Content v2.Content)

        /// Cross product of 3-vectors.
        static member public CrossProduct (v1: Vector, v2: Vector) =
            assert (v1.Kind = v2.Kind)
            assert (v1.Length = v2.Length)
            assert (v1.Length = 3)

            let a, b, c = v1.[0], v1.[1], v1.[2]
            let d, e, f = v2.[0], v2.[1], v2.[2]

            [| neg (c * e) + (b * f) ; (c * d) - (a * f); neg (b * d) + (a * e) |]
            |> Vector

        /// Computes a set of orthogonal vectors that span the same subspace as the given vectors.
        static member public Orthogonalize (vs: Vector list) =

            /// Computes one vector based on the allready found vectors.
            let rec calcNext (current: Vector) : Vector list -> Vector = function
                | [] -> current
                | v :: vs -> calcNext (current - Vector.Project (v, current)) vs

            /// Computes the vectors.
            let rec calc found = function
                | [] -> found
                | current :: rest -> calc ((calcNext current found) :: found) rest

            List.rev (calc [] vs)
