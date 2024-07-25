namespace Liyh.Kernel.LinearAlgebra

module rec Matrix =
    open System.Linq
    open Liyh.Utils
    open Liyh.Kernel.SumProd
    open Liyh.Kernel.LinearAlgebra.Vector

    /// Lists common types of matrix.
    type public MatrixKind =
        | MatrixKindDiagonal
        | MatrixKindIdentity
        | MatrixKindScalar
        | MatrixKind1x1
        | MatrixKindTriangular
        | MatrixKindZero
        | MatrixKindSymmetric
        | MatrixKindOrthogonal
        | MatrixKindRow
        | MatrixKindColumn
        | MatrixKindSparse

    /// Returns the common kinds of matrix that has been detected.
    let private matrixKind (matrix: SumProd[,]) =
        if   isDiagonalMatrix matrix   then [MatrixKindDiagonal; MatrixKindScalar]
        elif isIdentityMatrix matrix   then [MatrixKindIdentity; MatrixKindDiagonal; MatrixKindScalar]
        elif is1x1Matrix matrix        then [MatrixKind1x1; MatrixKindDiagonal; MatrixKindScalar]
        elif isScalarMatrix matrix     then [MatrixKindScalar]
        elif isTriangularMatrix matrix then [MatrixKindTriangular]
        elif isZeroMatrix matrix       then [MatrixKindZero]
        elif isSymetricMatrix matrix   then [MatrixKindSymmetric]
        elif isOrthogonalMatrix matrix then [MatrixKindOrthogonal]
        elif isRowMatrix matrix        then [MatrixKindRow]
        elif isColMatrix matrix        then [MatrixKindColumn]
        elif isSparseMatrix matrix     then [MatrixKindSparse]
                                       else []

    /// Convert the 2D array into an enumerable sequence.
    let private castMatrixIE (matrix: SumProd[,]) =
        matrix.Cast<SumProd>()

    /// Checks whether the matrix is sparse (the criterion is that the number of 0s is
    /// greater than the total number of elements).
    let private isSparseMatrix (matrix: SumProd[,]) =
        let ie = castMatrixIE matrix
        let czeros = ie.Count isZero

        2 * czeros > ie.Count()

    /// Checks if the matrix is diagonal.
    let private isDiagonalMatrix (matrix: SumProd[,]) =
        let mutable r = true

        for i = 0 to Array2D.length1 matrix - 1 do
            for j = 0 to Array2D.length2 matrix - 1 do
                if i <> j && matrix.[i, j] <> Zero then r <- false

        isSquareMatrix matrix && r

    /// Checks if the matrix is triangular.
    let private isTriangularMatrix (matrix: SumProd[,]) =

        let isLowerTriangular matrix =
            let mutable r = true

            for i = 0 to Array2D.length1 matrix - 1 do
                for j = i + 1 to Array2D.length1 matrix - 1 do
                    if matrix.[i, j] <> Zero then r <- false
            r
        
        let isUpperTriangular matrix =
            let mutable r = true

            for i = 0 to Array2D.length1 matrix - 1 do
                for j = 0 to i do
                    if matrix.[i, j] <> Zero then r <- false
            r

        isSquareMatrix matrix && (isLowerTriangular matrix || isUpperTriangular matrix)

    /// Checks if the matrix is orthogonal.
    let private isOrthogonalMatrix (matrix: SumProd[,]) =
        isSquareMatrix matrix && transpose matrix = inverse matrix

    /// Checks if the matrix is scalar.
    let private isScalarMatrix (matrix: SumProd[,]) =
        isDiagonalMatrix matrix && (diagonal matrix : SumProd array).All (( = ) matrix.[0, 0])

    /// Checks if the matrix is a 1x1 matrix.
    let private is1x1Matrix (matrix: SumProd[,]) =
        (Array2D.length1 matrix = Array2D.length2 matrix) && (Array2D.length1 matrix = 1)

    /// Checks if the matrix is the identity.
    let private isIdentityMatrix (matrix: SumProd[,]) =
        isDiagonalMatrix matrix && (diagonal matrix : SumProd array).All isOne

    /// Checks if the matrix is the null matrix.
    let private isZeroMatrix (matrix: SumProd[,]) =
        (castMatrixIE matrix).All isZero

    /// Checks if the matrix is symetric.
    let private isSymetricMatrix (matrix: SumProd[,]) =
        isSquareMatrix matrix && transpose matrix = matrix

    /// Checks if the matrix is a row vector.
    let private isRowMatrix (matrix: SumProd[,]) =
        Array2D.length1 matrix = 1

    /// Checks if the matrix is a column vector.
    let private isColMatrix (matrix: SumProd[,]) =
        Array2D.length2 matrix = 1

    /// Returns the dimension of the given matrix.
    let private dimension (matrix: _[,]) =
        Array2D.length1 matrix, Array2D.length2 matrix

    /// Checks if the matrix is square.
    let private isSquareMatrix (matrix: SumProd[,]) =
        let a, b = dimension matrix in a = b

    /// Checks whether the matrix contains elements that are all defined.
    let private isDefiniteMatrix (matrix: SumProd[,]) =
        (castMatrixIE matrix).All (( <> ) Undefined)

    /// Returns the transpose of the given matrix.
    let private transpose (matrix: SumProd[,]) =
        if isIdentityMatrix matrix || isZeroMatrix matrix then matrix
        else Array2D.init (Array2D.length2 matrix) (Array2D.length1 matrix) (fun i j -> matrix.[j, i])

    /// Returns the determinant of the given matrix.
    let private determinant (matrix: SumProd[,]) =
        assert (isSquareMatrix matrix)

        if isScalarMatrix matrix || isTriangularMatrix matrix then diagonalProduct matrix
        elif isZeroMatrix matrix then Zero
        else
            match Array2D.length2 matrix with
            | 0 -> Undefined
            | 1 -> matrix.[0, 0]
            | 2 -> matrix.[0, 0] * matrix.[1, 1] - matrix.[0, 1] * matrix.[1, 0]
            | width -> [| 0 .. width - 1 |] |> Array.sumBy(fun c -> matrix.[0, c] * cofactor matrix 0 c)

    /// Returns a submatrix from the given matrix, row and column.
    let private subMatrix (parent: SumProd[,]) row col =
        assert (Array2D.length1 parent >= row && Array2D.length2 parent >= col)

        let height, width = Array2D.length1 parent, Array2D.length2 parent
        let subHight, subWidth = height - 1, width - 1
        let sub = Array2D.create subHight subWidth Undefined

        Array2D.blit parent 0 0 sub 0 0 row col
        Array2D.blit parent 0 (col + 1) sub 0 col row (subWidth - col)
        Array2D.blit parent (row + 1) 0 sub row 0 (subHight - row) col
        Array2D.blit parent (row + 1) (col + 1) sub row col (subHight - row) (subWidth - col)

        sub

    /// Returns the minor (i.e. the determinant of a submatrix) from the given matrix, row and column.
    let private minor (matrix: SumProd[,]) row col =
        subMatrix matrix row col |> determinant

    /// Returns the cofactor of the given matrix, row and column.
    let private cofactor (matrix: SumProd[,]) row col =
        let minor = minor matrix row col

        match (row + col) % 2 with
        | 0 -> minor
        | _ -> neg minor

    /// Checks whether the matrix is invertible.
    let private invertible (matrix: SumProd[,]) =
        isSquareMatrix matrix && determinant matrix <> Zero

    /// Inverse the given matrix.
    let private inverse (matrix: SumProd[,]) =
        assert (invertible matrix)

        let det = determinant matrix
        Array2D.mapi (fun r c _ -> cofactor matrix r c) matrix
        |> transpose |> Array2D.map (fun n -> n / det)

    /// Returns the diagonal of the given matrix.
    let private diagonal (matrix: SumProd[,]) =
        assert (isSquareMatrix matrix)
        [| for i = 0 to Array2D.length1 matrix - 1 do matrix.[i, i] |]

    /// Returns the trace of the given matrix.
    let private trace (matrix: SumProd[,]) =
        diagonal matrix |> Array.sum

    /// Returns the product of each elements of the main diagonal of the given matrix.
    let private diagonalProduct (matrix: SumProd[,]) =
        diagonal matrix |> Array.reduce ( * )

    /// Addition of matrix.
    let private addition (m1: SumProd[,]) (m2: SumProd[,]) =
        assert (dimension m1 = dimension m2)
        Array2D.init (Array2D.length1 m1) (Array2D.length2 m2) (fun i j -> m1.[i, j] + m2.[i, j])

    /// Multiplication of matrix.
    let private multiplication (m1: SumProd[,]) (m2: SumProd[,]) =
        let height1, height2 = Array2D.length1 m1, Array2D.length1 m2
        let width1, width2 = Array2D.length2 m1, Array2D.length2 m2

        assert(width1 = height2)

        let inner row col = Array.map2 ( * ) m1.[row, *] m2.[*, col] |> Array.sum

        let result =
            if isZeroMatrix m1 || isZeroMatrix m2 then Array2D.init height1 width2 (fun _ _ -> Zero)
            elif isIdentityMatrix m1 then m2
            elif isIdentityMatrix m2 then m1
            else Array2D.init height1 width2 inner

        height1, width2, Some result

    /// The size-identity matrix.
    let private identity size =
        assert (size > 0)
        Array2D.init size size (fun r c -> if r = c then One else Zero)

    /// Get a specific column of the given matrix.
    let private column (m: SumProd[,]) (index: int) =
        [| 0 .. Array2D.length1 m - 1 |] |> Array.map (fun z -> m.[z, index])

    /// Get all columns of the given matrix.
    let private columns (m: SumProd[,]) =
        [| 0 .. Array2D.length2 m - 1 |] |> Array.map (column m)

    /// Tensor product / direct product / kronecker product of two matrix.
    let private directProduct (m1: SumProd[,]) (m2: SumProd[,]) =
        let (m, n), (p, q) = dimension m1, dimension m2
        let inner i j = (m1.[i/p, j/q]) * (m2.[i%p, j%q])

        Array2D.init (p * m) (q * n) inner

    /// Term by term multiplication of two matrix.
    let private hadamardProduct (m1: SumProd[,]) (m2: SumProd[,]) =
        Array2D.mapi (fun i j x -> x * m2.[i, j]) m1

    /// Concatenation of two matrix vertically.
    let private vconcat (m1: SumProd[,]) (m2: SumProd[,]) =
        let (m, n), (p, q) = dimension m1, dimension m2
        assert (n = q)

        let result = Array2D.zeroCreate (m + p) n
        Array2D.blit m1 0 0 result 0 0 m n
        Array2D.blit m2 0 0 result m 0 p q

        result

    /// Concatenation of two matrix horizontally.
    let private hconcat (m1: SumProd[,]) (m2: SumProd[,]) =
        let (m, n), (p, q) = dimension m1, dimension m2
        assert (m = p)

        let result = Array2D.zeroCreate m (n + q)

        Array2D.blit m1 0 0 result 0 0 m n
        Array2D.blit m2 0 0 result 0 n p q

        result

    /// Check if the given matrix contains only numeric values.
    let private isNumericMatrix =
        castMatrixIE >> Seq.forall isNumeric

    /// Solve Ax=0. For example,
    ///
    ///     | 3x + 2y - 4z = 3
    ///     | 2x + 3y + 3z = 15
    ///     | 5x - 3y + z  = 14
    ///
    /// then,
    /// 
    ///            x   y   z  CST
    ///         [| 3;  2; -4; -3  |]
    ///     A = [| 2;  3;  3; -15 |]
    ///         [| 5; -3;  1; -14 |]
    /// 
    let private solve (matrix: float[,]) =
        let n, _ = dimension matrix
        let result = Array.init n (konst 0.0)

        for i = 0 to n - 1 do
            let mutable pivotRow = i

            (* Find the row with the largest absolute value in the first column *)

            for j = i + 1 to n - 1 do
                if abs matrix.[j, i] > abs matrix.[pivotRow, i]
                then pivotRow <- j

            (* Swap that row with the first row *)

            if pivotRow <> i then
                for j = i to n do
                    let tmp = matrix.[i, j]
                    matrix.[i, j] <- matrix.[pivotRow, j]
                    matrix.[pivotRow, j] <- tmp

            (* Divide the first row by the pivot element to make it equal to 1 *)

            for j = i + 1 to n - 1 do
                let factor = matrix.[j, i] / matrix.[i, i]
                for k = i to n do
                    matrix.[j, k] <- matrix.[j, k] - factor * matrix.[i, k]

        (* Back-substitute to obtain the values of the unknowns *)

        for i = n - 1 downto 0 do
            let sum = Array.map (fun j -> matrix.[i, j] * result.[j]) [| i + 1 .. n - 1 |] |> Array.sum
            result.[i] <- (matrix.[i, n] - sum) / matrix.[i, i]

        if result.Contains nan then None else Some result

    /// Return the clockwise rotation of the given matrix.
    let private rotate (matrix: SumProd[,]) =
        let n, m = dimension matrix
        Array2D.init m n (fun row col -> Array2D.get matrix (n - col - 1) row)

    let private latex (matrix: SumProd[,]) =
        let n, m = dimension matrix

        let tmp =
            [| for i = 0 to n - 1 do
                for j = 0 to m - 1 do
                    sprintf "%s%s" (matrix.[i, j].ToLatex)
                                   (if j = m - 1 then "" else "&")
                @"\\" |]

        sprintf @"\begin{bmatrix}%s\end{bmatrix}"
        <| System.String.Join("", tmp)

    /// Represents a SumProd matrix in the sense of linear algebra and provides the standard operations.
    type public Matrix(nRows: int, nCols: int, content: SumProd[,] option) =
    
        /// The content of a matrix is encoded as a two-dimensional array using `array2D`.
        let content =
            assert (nRows > 0 && nCols > 0)

            match content with
            | Some data -> data
            | None -> Array2D.create nRows nCols Undefined

        new (content: SumProd[,]) =
            Matrix(Array2D.length1 content, Array2D.length2 content, Some content)

        new (content: int[,]) =
            Matrix(Array2D.map (fun (x: int) -> Integer (bigint x)) content)

        new (content: float[,]) =
            Matrix(Array2D.map Float content)

        new (content: float[][]) =
            Matrix(array2D content)

        new (content: int[][]) =
            Matrix(array2D content)

        new (content: SumProd[][]) =
            Matrix(array2D content)

        new (content: Vector) =
            match content.Kind with
            | RowVector -> Matrix [| content.Content |]
            | ColumnVector -> Matrix [| for x in content.Content -> [| x |] |]

        /// Returns the Array2D content of the matrix.
        member public __.Content = content

        member public __.GetNRows = nRows
        member public __.GetNCols = nCols
        member public __.Dimension = dimension content
        member public __.Transpose = Matrix(transpose content)
        member public __.Diagonal = diagonal content
        member public __.Determinant = determinant content
        member public __.SubMatrix row col = Matrix(subMatrix content row col)
        member public __.Minor row col = minor content row col
        member public __.Cofactor row col = cofactor content row col
        member public __.Invertible = invertible content
        member public __.Inverse = Matrix (inverse content)
        member public __.Trace = trace content
        member public __.Kind = matrixKind content
        member public __.Simplify = __.Map simp
        member public __.Column = column content
        member public __.Columns = columns content

        member public __.Map (mapper: SumProd -> SumProd) = Matrix(Array2D.map mapper content)
        member public __.Map (mapper: SumProd -> int) = Matrix(Array2D.map mapper content)
        member public __.Map (mapper: SumProd -> float) = Matrix(Array2D.map mapper content)

        member __.ToVector () =
            assert (isColMatrix content || isRowMatrix content)

        member public __.ToLatex = latex content
        override __.ToString () = sprintf "%A" content

        member public __.Item
            with get(r, c) = content.[r, c]

        static member public ( + ) (m1: Matrix, m2: Matrix) = addition m1.Content m2.Content |> Matrix
        static member public ( * ) (m1: Matrix, m2: Matrix) = multiplication m1.Content m2.Content |> Matrix
        static member public ( * ) (m1: Matrix, v1: Vector) = assert (v1.Kind = ColumnVector); m1 * Matrix v1
        static member public ( * ) (v1: Vector, m1: Matrix) = assert (v1.Kind = RowVector); Matrix v1 * m1

        static member public DirectProduct (m1: Matrix, m2: Matrix) = directProduct m1.Content m2.Content |> Matrix
        static member public HadamardProduct (m1: Matrix, m2: Matrix) = hadamardProduct m1.Content m2.Content |> Matrix
        static member public Vconcat (m1: Matrix, m2: Matrix) = vconcat m1.Content m2.Content |> Matrix
        static member public Hconcat (m1: Matrix, m2: Matrix) = hconcat m1.Content m2.Content |> Matrix

        static member public ( ++ ) (m1: Matrix, m2: Matrix) = Matrix.Hconcat (m1, m2)

        /// Multiply the two matrices to the given times.
        static member public ( *** ) (m: Matrix, power: int) =

            let rec inner m power =
                if power = 1 then m
                else let p = inner m (power / 2)
                     if power % 2 = 0 then p * p
                     else p * p * m

            if power = 0 then Matrix.Identity m.GetNCols else inner m power

        /// Creates a matrix from a array of column-vectors.
        static member public Create (vs: Vector array) = 
            Array2D.init vs.[0].Length vs.Length (fun r c -> vs.[c].[r])
            |> Matrix

        /// Creates a matrix with an generator-function (the row `r` and col `c` of the matrix will have a value `f(r, c)`).
        static member public Create (rows, cols, f: int -> int -> SumProd) =
            Array2D.init rows cols f |> Matrix

        /// Creates a matrix with an generator-function (the row `r` and col `c` of the matrix will have a value `f(r, c)`).
        static member public Create (rows, cols, f: int -> int -> int) =
            Array2D.init rows cols f |> Matrix

        /// Creates a matrix with an generator-function (the row `r` and col `c` of the matrix will have a value `f(r, c)`).
        static member public Create (rows, cols, f: int -> int -> float) =
            Array2D.init rows cols f |> Matrix

        /// Generates the identity matrix of the given size.
        static member public Identity size = Matrix (identity size)

        /// Solve the linear equations Ax=B by performing the gaussian elimination.
        /// If there is no solution, then return `None`.
        static member public Solve (matrix: Matrix) =
            let content = matrix.Content
            assert (isNumericMatrix content)

            match solve (Array2D.map evalLitConstAsFloat content) with
            | Some result -> Some (Vector result)
            | None -> None

        /// Return the clockwise rotation of the original matrix.
        static member public Rotate (matrix: Matrix) =
            Matrix(rotate matrix.Content)

        /// Build a new matrix from vectors.
        static member public FromVectors (vectors: Vector seq) =
            if vectors.All (fun v -> v.IsRowVector) then
                Matrix(Array.map (fun (v: Vector) -> v.Content) (Seq.toArray vectors))

            elif vectors.All (fun v -> v.IsColVector) then
                let tmp = Array.map (fun (v: Vector) -> Matrix v) (Seq.toArray vectors)
                Array.reduce (curry Matrix.Hconcat) tmp

            else
                failwith "<?>"

    // http://www.fssnip.net/3p/title/QRdecomoposition-of-a-squarematrix-using-the-GramSchmidt-method
    // Il marche pas son algorithme là

