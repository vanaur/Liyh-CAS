namespace Liyh.Kernel

#nowarn "3391"
#nowarn "25"

/// This module covers vector, matrix and tensor algebra.
module public rec MultiLinearAlgebra =
    open System
    open Liyh.Kernel
    open Liyh.Utils

    /// This module deals with classical vector algebra over SumPow.
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
        /// Note: modifying the return value does not modify the initial vector.
        let public components (Vector components) =
            if Array.isEmpty components then
                raise VectorHasNoComponentException

            Array.copy components

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

        let public size (Vector components) =
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

    /// This module deals with classical matrix algebra over SumPow.
    module public Matrix =
        open System.Collections.Generic
        open Vector

        exception public IncompatibleMatrixException of Matrix seq
        exception public MatrixHasNoComponentException
        exception public NotASquareMatrixException of Matrix
        exception public SingularMatrixException of Matrix // det = 0

        [<Symbolic>]
        type public Matrix =
            | Matrix of SumPow[,]

            member this.Item
                with get (i, j) =
                    let (Matrix components) = this
                    components.[i, j]

            interface ISymbolic with
                member this.ToSymbolic() = toSymbolic this
                member this.ToLatex() = Some(toLatex this)
                member this.ToLatexOrString() = toLatex this
                member this.Hash = hash this

            static member op_Addition(a: Matrix, b: Matrix) = Operations.addition a b
            static member op_Subtraction(a: Matrix, b: Matrix) = Operations.subtraction a b
            static member op_Multiply(a: Matrix, b: Matrix) = Operations.multiplication a b
            static member op_Multiply(scalar: SumPow, m: Matrix) = Operations.scalarMultiplication scalar m
            static member op_Division(m: Matrix, scalar: SumPow) = Operations.scalarDivision m scalar
            static member Pow(m: Matrix, n: int) = Operations.pown m n

        /// Returns an `Array2D` of components.
        /// Note: modifying the return value does not modify the initial matrix.
        let public components (Matrix components) =
            if Array2D.length1 components = 0
            && Array2D.length2 components = 0 then
                raise MatrixHasNoComponentException

            Array2D.copy components

        let private toSymbolic (matrix: Matrix) =
            let cs = components matrix

            let rows = [ for row in 0 .. Array2D.length1 cs - 1 -> List.ofArray cs.[row, *] ]
            let args = List.map (fun a -> { atom = Identifier "Row"; attributes = List.map (fun r -> null, Atomic.toSymbolic r) a }) rows
            let args = List.map (fun a -> null, a) args

            { atom = Identifier "Matrix"
              attributes = args }
        
        let private toLatex (matrix: Matrix) =
            let cs = components matrix
            let cs = Array2D.map toLatexOrString cs
            let rows = [| for row in 0 .. Array2D.length1 cs - 1 -> cs.[row, *] |]
            let rows = Array.map (fun (c: string array) -> System.String.Join(" & ", c)) rows

            let env = sprintf @"\begin{bmatrix} %s \end{bmatrix}"
            let body = System.String.Join(@" \\ ", rows)

            env body

        /// Generates a matrix of a given size based on the specified generating function.
        let public generate (rows: int) (cols: int) (f: int -> int -> SumPow) =
            Matrix (Array2D.init rows cols f)

        /// Generates a matrix of a given size and of random integer components.
        /// This is mainly used for testing and debuging purposes.
        let public generateRandom (rows: int) (cols: int) =
            let rnd = new Random()
            [| for r in 0 .. rows - 1 -> [| for c in 0 .. cols - 1 ->  Const (double (rnd.Next(min r c, max r c))) |] |]
            |> fromArray

        let public size (Matrix components) =
            Array2D.length1 components, Array2D.length2 components

        /// Converts an array of arrays into a matrix.
        let public fromArray (components: SumPow array array) =
            let rows = Array.length components
            let cols = Array.length (Array.head components)

            let mutable matrix = Array2D.create rows cols (Const Zero)

            for i in 0 .. rows - 1 do
                for j in 0 .. cols - 1 do
                    matrix.[i, j] <- components.[i].[j]

            Matrix matrix

        /// Specifies what a uni-dimenstional matrix (a covariant or contravariant vector) must look like.
        [<RequireQualifiedAccess; Struct; NoEquality; NoComparison>]
        type public Matrix1D =
            | RowVector
            | ColumnVector

        /// Gets the matrix representation of the given vector.
        let public fromVector (Vector cs) (kind: Matrix1D) =
            match kind with
            | Matrix1D.RowVector -> fromArray [| cs |]
            | Matrix1D.ColumnVector -> fromArray [| for i = 0 to Array.length cs - 1 do [| cs.[i] |] |]

        module private Operations =

            let public addition (m1: Matrix) (m2: Matrix) =
                let cs1 = components m1
                let cs2 = components m2

                if Array2D.length1 cs1 <> Array2D.length1 cs2
                || Array2D.length2 cs1 <> Array2D.length2 cs2 then
                    raise (IncompatibleMatrixException [ m1; m2 ])

                let l1 = Array2D.length1 cs1
                let l2 = Array2D.length2 cs1

                let mutable result = Array2D.create l1 l2 (Const Zero)

                for i = 0 to l1 - 1 do
                    for j = 0 to l2 - 1 do
                        result.[i, j] <- cs1.[i, j] + cs2.[i, j]

                Matrix result

            let public subtraction (m1: Matrix) (m2: Matrix) =
                let cs1 = components m1
                let cs2 = components m2

                if Array2D.length1 cs1 <> Array2D.length1 cs2
                || Array2D.length2 cs1 <> Array2D.length2 cs2 then
                    raise (IncompatibleMatrixException [ m1; m2 ])

                let l1 = Array2D.length1 cs1
                let l2 = Array2D.length2 cs1

                let mutable result = Array2D.create l1 l2 (Const Zero)

                for i = 0 to l1 - 1 do
                    for j = 0 to l2 - 1 do
                        result.[i, j] <- cs1.[i, j] - cs2.[i, j]

                Matrix result

            /// Multiply each component of the given matrix by the given scalar.
            let public scalarMultiplication (scalar: SumPow) (m: Matrix) =
                Matrix (Array2D.map (( * ) scalar) (components m))

            /// Divise each component of the given matrix by the given scalar.
            let public scalarDivision (m: Matrix) (scalar: SumPow) =
                Matrix (Array2D.map (fun c -> c / scalar) (components m))

            /// Implements naive matrix multiplication.
            let public multiplication (m1: Matrix) (m2: Matrix) =
                let cs1 = components m1
                let cs2 = components m2

                let rows1 = Array2D.length1 cs1
                let cols1 = Array2D.length2 cs1
                let rows2 = Array2D.length1 cs2
                let cols2 = Array2D.length2 cs2

                if cols1 <> rows2 then
                    raise (IncompatibleMatrixException [ m1; m2 ])

                let mutable result = Array2D.create rows1 cols2 (Const Zero)

                for i in 0 .. rows1 - 1 do
                    for j in 0 .. cols2 - 1 do
                        for k in 0 .. cols1 - 1 do
                            result.[i, j] <- result.[i, j] + cs1.[i, k] * cs2.[k, j]

                Matrix result

            /// Exponentiate the given square matrix to the given integer.
            let rec public pown (matrix: Matrix) (n: int) =
                if not (isSquareMatrix matrix) then
                    raise (NotASquareMatrixException matrix)

                let rec loop (m: Matrix) (n: float) (acc: Matrix) =
                    printfn "%A" n
                    if n <= 1 then acc * m
                    else let p = if floor (float n % 2.) = 0. then acc else acc * m
                         loop (m * m) (n / 2.) p

                if n = 0 then idMatrix (fst (size matrix))
                elif n > 0 then (loop matrix n (idMatrix (fst (size matrix))))
                else
                    match tryInverse matrix with
                    | None -> raise (SingularMatrixException matrix)
                    | Some inv -> pown inv (abs n)

        let public simplifyComponents (m: Matrix) =
            let cs = components m
            Matrix (Array2D.map Simplification.simplify cs)

        /// Check if the matrix is square.
        let public isSquareMatrix (m: Matrix) =
            let cs = components m
            Array2D.length1 cs = Array2D.length2 cs

        /// Returns the main diagonal of the given matrix.
        let public diagonal (m: Matrix) =
            if not (isSquareMatrix m) then
                raise (NotASquareMatrixException m)

            let cs = components m

            let l = min (Array2D.length1 cs) (Array2D.length2 cs) - 1
            [| for i in 0 .. l -> cs.[i, i] |]

        /// Compute the sum of the diagonal of the given matrix.
        let public trace (m: Matrix) =
            Array.reduce ( + ) (diagonal m)
            |> Simplification.simplify

        /// Use the Laplace expansion method to compute the determinant of the given matrix.
        /// Note: this method is not efficient for large matrix (time complexity: O(n!)).
        /// See https://en.wikipedia.org/wiki/Laplace_expansion.
        let public determinant (m: Matrix) =
            if not (isSquareMatrix m) then
                raise (NotASquareMatrixException m)

            let submatrix (matrix: SumPow[,]) (row: int) (col: int) =
                let n = Array2D.length1 matrix
                Array2D.init (n - 1) (n - 1) (fun i j ->
                    let newRow = if i < row then i else i + 1
                    let newCol = if j < col then j else j + 1
                    matrix.[newRow, newCol])

            (* We hard-code the determinants for small matrices to gain some performance in the loop. *)

            let inline det1x1 (matrix: SumPow[,]) = matrix.[0, 0]
            let inline det2x2 (matrix: SumPow[,]) = (matrix.[0, 0] * matrix.[1, 1]) - (matrix.[0, 1] * matrix.[1, 0])
            let inline det3x3 (matrix: SumPow[,]) = matrix.[0, 0] * (matrix.[1, 1] * matrix.[2, 2] - matrix.[1, 2] * matrix.[2, 1]) - matrix.[0, 1] * (matrix.[1, 0] * matrix.[2, 2] - matrix.[1, 2] * matrix.[2, 0]) + matrix.[0, 2] * (matrix.[1, 0] * matrix.[2, 1] - matrix.[1, 1] * matrix.[2, 0]) 
            let inline det4x4 (matrix: SumPow[,]) = matrix.[0, 0] * (matrix.[1, 1] * (matrix.[2, 2] * matrix.[3, 3] - matrix.[2, 3] * matrix.[3, 2]) - matrix.[1, 2] * (matrix.[2, 1] * matrix.[3, 3] - matrix.[2, 3] * matrix.[3, 1]) + matrix.[1, 3] * (matrix.[2, 1] * matrix.[3, 2] - matrix.[2, 2] * matrix.[3, 1])) - matrix.[0, 1] * (matrix.[1, 0] * (matrix.[2, 2] * matrix.[3, 3] - matrix.[2, 3] * matrix.[3, 2]) - matrix.[1, 2] * (matrix.[2, 0] * matrix.[3, 3] - matrix.[2, 3] * matrix.[3, 0]) + matrix.[1, 3] * (matrix.[2, 0] * matrix.[3, 2] - matrix.[2, 2] * matrix.[3, 0])) + matrix.[0, 2] * (matrix.[1, 0] * (matrix.[2, 1] * matrix.[3, 3] - matrix.[2, 3] * matrix.[3, 1]) - matrix.[1, 1] * (matrix.[2, 0] * matrix.[3, 3] - matrix.[2, 3] * matrix.[3, 0]) + matrix.[1, 3] * (matrix.[2, 0] * matrix.[3, 1] - matrix.[2, 1] * matrix.[3, 0])) - matrix.[0, 3] * (matrix.[1, 0] * (matrix.[2, 1] * matrix.[3, 2] - matrix.[2, 2] * matrix.[3, 1]) - matrix.[1, 1] * (matrix.[2, 0] * matrix.[3, 2] - matrix.[2, 2] * matrix.[3, 0]) + matrix.[1, 2] * (matrix.[2, 0] * matrix.[3, 1] - matrix.[2, 1] * matrix.[3, 0]))

            let rec loop (matrix: SumPow[,]) =
                match Array2D.length1 matrix with
                | 0 -> failwith "??" // May not happen
                | 1 -> det1x1 matrix
                | 2 -> det2x2 matrix
                | 3 -> det3x3 matrix
                | 4 -> det4x4 matrix
                | n ->
                    let mutable det = Const Zero
                    for col in 0 .. n - 1 do
                        let coMatrix = loop (submatrix matrix 0 col)
                        let coFactor = matrix.[0, col] * (if col % 2 = 0 then 1 else -1) * coMatrix
                        det <- det + coFactor
                    det

            loop (components m)
            |> Simplification.simplify

        /// Returns the transpose of the given matrix.
        /// See https://en.wikipedia.org/wiki/Transpose.
        let public transpose (m: Matrix) =
            let cs = components m
            let l1 = Array2D.length1 cs
            let l2 = Array2D.length2 cs

            Matrix (Array2D.init l2 l1 (fun i j -> m.[j, i]))

        /// Compute the Kronecker product (~"tensor product") of the two given matrix.
        /// See https://en.wikipedia.org/wiki/Kronecker_product.
        let public kroneckerProduct (m1: Matrix) (m2: Matrix) =
            let cs1 = components m1
            let cs2 = components m2

            let aRows = Array2D.length1 cs1
            let aCols = Array2D.length2 cs1
            let bRows = Array2D.length1 cs2
            let bCols = Array2D.length2 cs2

            let mutable result = Array2D.zeroCreate (aRows * bRows) (aCols * bCols)

            for i in 0 .. aRows - 1 do
                for j in 0 .. aCols - 1 do
                    for k in 0 .. bRows - 1 do
                        for l in 0 .. bCols - 1 do
                            result.[i * bRows + k, j * bCols + l] <-
                                Simplification.simplify (cs1.[i, j] * cs2.[k, l])

            Matrix result

        /// Compute the Hadamard product of the two given matrix.
        /// See https://en.wikipedia.org/wiki/Hadamard_product_(matrices).
        let public hadamardProduct (m1: Matrix) (m2: Matrix) =
            let cs1 = components m1
            let cs2 = components m2

            if Array2D.length1 cs1 <> Array2D.length1 cs2
            || Array2D.length2 cs1 <> Array2D.length2 cs2 then
                raise (IncompatibleMatrixException [ m1; m2 ])

            let l1 = Array2D.length1 cs1
            let l2 = Array2D.length2 cs1

            let mutable result = Array2D.create l1 l2 (Const Zero)

            for i = 0 to l1 - 1 do
                for j = 0 to l2 - 1 do
                    result.[i, j] <- cs1.[i, j] * cs2.[i, j]

            Matrix result

        /// The identity matrix of the given size.
        let public idMatrix (size: int) =
            if size <= 0 then
                raise MatrixHasNoComponentException

            Matrix (Array2D.init size size (fun i j -> if i = j then Const One else Const Zero))

        /// Check if the given matrix is the identity matrix.
        let public isIdentity (m: Matrix) =
            if not (isSquareMatrix m) then
                raise (NotASquareMatrixException m)

            let cs = components (simplifyComponents m)
            m = idMatrix (Array2D.length1 cs)

        /// Review the submatrix indicated.
        let public subMatrix (matrix: Matrix) (row: int) (col: int) =
            let cs = components matrix
            let rows = Array2D.length1 cs
            let cols = Array2D.length2 cs

            let sub = Array2D.zeroCreate (rows - 1) (cols - 1)
            
            let mutable subRow = 0
            for r in 0 .. (rows - 1) do
                if r <> row then
                    let mutable subCol = 0
                    for c in 0 .. (cols - 1) do
                        if c <> col then
                            sub.[subRow, subCol] <- matrix.[r, c]
                            subCol <- subCol + 1
                    subRow <- subRow + 1

            Matrix sub

        /// Returns the co-factor of the indicated sub-matrix.
        let public cofactor (matrix: Matrix) (row: int) (col: int) =
            let sub = subMatrix matrix row col
            let det = determinant sub
            let sign = if (row + col) % 2 = 0 then 1 else -1
            sign * det

        /// Returns the matrix of co-factors.
        let public cofactorMatrix (matrix: Matrix) =
            if not (isSquareMatrix matrix) then
                raise (NotASquareMatrixException matrix)

            let cs = components matrix
            let rows = Array2D.length1 cs
            let cols = Array2D.length2 cs

            let mutable result = Array2D.zeroCreate rows cols
            for i in 0 .. (rows - 1) do
                for j in 0 .. (cols - 1) do
                    result.[i, j] <- cofactor matrix i j

            Matrix result

        /// Returns the transpo of the cofactor matrix of the given matrix.
        let public adjoint (matrix: Matrix) =
            if not (isSquareMatrix matrix) then
                raise (NotASquareMatrixException matrix)

            transpose (cofactorMatrix matrix)

        /// Returns the inverse of the given square matrix if it is non-singular, otherwise `None`.
        let public tryInverse (matrix: Matrix) =
            if not (isSquareMatrix matrix) then
                raise (NotASquareMatrixException matrix)

            let cs = components matrix
            let rows = Array2D.length1 cs
            let cols = Array2D.length2 cs

            let det = determinant matrix
            if Misc.isZero det then None else

            let adjoint = adjoint matrix
            let mutable result = Array2D.zeroCreate rows cols

            for i in 0 .. rows - 1 do
                for j in 0 .. cols - 1 do
                    result.[i, j] <- Simplification.simplify (adjoint.[i, j] / det)

            Some (Matrix result)

        /// Returns the QR decomposition of the given matrix (using Gram-Schmidt process).
        /// The matrix Q is an orthogonal and the matrix R is a upper triangular matrix.
        let public qrDecomposition (matrix: Matrix) =
            let cs = components matrix

            let m = Array2D.length1 cs
            let n = Array2D.length2 cs

            if m < n then
                raise (IncompatibleMatrixException [ matrix ])
            
            let columns = [| for j in 0 .. n - 1 -> Vector [| for i in 0 .. m - 1 -> cs.[i, j] |] |]
            let normsVs = gramSchmidtNormalized columns
            let Q = Array2D.init m n (fun r c -> normsVs.[r].[c])
            let f r c = if r <= c then dotProduct normsVs.[r] columns.[c] else Const Zero
            let R = Array2D.init m n f

            Matrix Q, Matrix R

        /// Returns the characteristic polynomial of the given matrix.
        let public characteristicPolynomial (matrix: Matrix) (variable: SumPow) =
            if not (isSquareMatrix matrix) then
                raise (NotASquareMatrixException matrix)

            let λI = variable * idMatrix (fst (size matrix))
            determinant (matrix - λI)

        /// Find the numerical eigenvalues of the given matrix.
        let public nEigenvalues (matrix: Matrix) (eps: double) (maxIterations: int) =
            let name = Name "_λ"
            let p = characteristicPolynomial matrix name
            let p, _ = Polynomial.Pattern.asUnivariatePolynomial name [] p

            let (Some nup) = Polynomial.NumericEvaluation.tryNumericUnivariatePolynomial p
            Polynomial.NumericEvaluation.findRoots nup eps maxIterations

        (* NOTE: the process below is extremely slow for some as yet unclear reason... *)

        /// Find the numerical eigenvalues and eigenvectors of the given matrix.
        let public ndiagonalize (matrix: Matrix) (maxIterations: int) (values: Dictionary<string, Constant>) =
            if not (isSquareMatrix matrix) then
                raise (NotASquareMatrixException matrix)

            let cs = asNumeric matrix values
            let n = Array2D.length1 cs

            let mutable B = fromNumeric (Array2D.copy cs)
            let mutable U = idMatrix n

            for _ in 0 .. maxIterations - 1 do
                let Q, R = qrDecomposition B
                let Q, R = fromNumeric (asNumeric Q values), fromNumeric (asNumeric R values)

                B <- R * Q
                U <- U * Q

            // The eigenvalues are on the diagonal of the B matrix.
            let eigenvalues = diagonal B

            // The eigenvectors are the columns of the U matrix.
            let eigenvectors = [| for j in 0 .. n - 1 -> Vector [| for i in 0 .. n - 1 -> U.[i, j] |] |]

            eigenvalues, eigenvectors

        /// Transpose the given matrix and take the conjugate of each entry.
        let public hermitianTranspose (matrix: Matrix) =
            let cs = components (transpose matrix)
            Matrix (Array2D.map (fun e -> Simplification.simplify (Fun("Conj", [ e ]))) cs) // need good support for complexes...

        /// Check if the given matrix is self-adjoint (equals its hermitian transpose).
        let public isSelfAdjoint (matrix: Matrix) =
            matrix = hermitianTranspose matrix

        /// Evaluates each component of the given matrix in approximate form.
        let public asNumeric (Matrix cs) (values: Dictionary<string, Constant>): double[,] =
            Array2D.map (flip NumericEvaluation.evaluate values >> toDouble) cs

        /// Converts a matrix of numbers into our matrix representation.
        let public fromNumeric (matrix: double[,]): Matrix =
            Matrix (Array2D.map (Constant >> Const) matrix)

    module public Tensor =

        type public Tensor =
            { indices: TensorIndex list
              dimension: int
              components: SumPow[] option }
        
        and public TensorIndex = Variance * string

        and public Variance =
        | Covariant
        | Contravariant
