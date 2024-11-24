namespace Liyh.Kernel

#nowarn "3391"
#nowarn "25"

/// This module covers vector, matrix and tensor algebra.
module public rec LinearAlgebra =
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

        /// Returns the components of the vector.
        /// Note: modifying the return value does not modify the initial vector.
        let public copyFreeComponents (Vector components) =
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
                let cs1 = copyFreeComponents v1
                let cs2 = copyFreeComponents v2

                if Array.length cs1 <> Array.length cs2 then
                    raise (VectorsHaveDifferentLengthException [ v1; v2 ])

                Vector (Array.map2 ( + ) cs1 cs2) |> simplifyComponents

            let public subtraction (v1: Vector) (v2: Vector) =
                let cs1 = copyFreeComponents v1
                let cs2 = copyFreeComponents v2

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
            let cs1 = copyFreeComponents v1
            let cs2 = copyFreeComponents v2

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
            let cs1 = copyFreeComponents v1
            let cs2 = copyFreeComponents v2

            if Array.length cs1 <> Array.length cs2 then
                raise (VectorsHaveDifferentLengthException [ v1; v2 ])

            let arg = dotProduct v1 v2 / (enorm v1 * enorm v2)
            Fun("Cos", [ arg ]) |> Simplification.simplify

        /// Project the vector `v1` onto the vector `v2`.
        /// See https://en.wikipedia.org/wiki/Vector_projection.
        let public project (v1: Vector) (v2: Vector) =
            let cs1 = copyFreeComponents v1
            let cs2 = copyFreeComponents v2

            if Array.length cs1 <> Array.length cs2 then
                raise (VectorsHaveDifferentLengthException [ v1; v2 ])

            let num = dotProduct v2 v1
            let den = dotProduct v1 v1

            Operations.scalarMultiplication (num / den) v1
            |> simplifyComponents

        /// Returns the cross-product of the two given vectors.
        /// See https://en.wikipedia.org/wiki/Cross_product.
        let public crossProduct (v1: Vector) (v2: Vector) =
            let cs1 = copyFreeComponents v1
            let cs2 = copyFreeComponents v2

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

        open System.Threading.Tasks
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

        /// Returns an `Array2D` of components.
        /// Note: modifying the return value do modify the initial matrix.
        let public copyFreeComponents (Matrix components) =
            if Array2D.length1 components = 0
            && Array2D.length2 components = 0 then
                raise MatrixHasNoComponentException

            components

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

        /// Returns the columns of the given matrix.
        let public getColumns (matrix: Matrix) =
            let cs = components matrix

            [| for col in 0 .. Array2D.length2 cs - 1 -> Array.ofSeq (Array2D.column col cs) |]

        /// Returns the rows of the given matrix.
        let public getRows (matrix: Matrix) =
            let cs = components matrix

            [| for row in 0 .. Array2D.length1 cs - 1 -> Array.ofSeq (Array2D.row row cs) |]

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

        /// Converts an array2d into a matrix.
        let public fromArray2D (components: SumPow array2d) =
            Matrix components

        /// Create a matrix where each column corresponds to one of the given vectors.
        let public fromVectors (vectors: Vector array) =
            if Array.isEmpty vectors then
                raise MatrixHasNoComponentException

            let m = Array.length vectors
            let n = Vector.size (Array.head vectors)

            Matrix (Array2D.init m n (fun i j -> vectors.[i].[j])) |> transpose

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

        /// This module implements the parallel Strassen matrix multiplication algorithm.
        /// See https://en.wikipedia.org/wiki/Strassen_algorithm.
        module private Strassen =

            /// Splits the given matrix in four smaller matrices.
            let private splitMatrix (matrix: SumPow[,]) =
                let n = Array2D.length1 matrix / 2
                let m = Array2D.length2 matrix / 2

                let A11 = Array2D.init n m (fun i j -> matrix.[i, j])
                let A12 = Array2D.init n m (fun i j -> matrix.[i, j + m])
                let A21 = Array2D.init n m (fun i j -> matrix.[i + n, j])
                let A22 = Array2D.init n m (fun i j -> matrix.[i + n, j + m])

                A11, A12, A21, A22

            /// Builds a matrix from the four given matrices.
            let private mergeMatrix (c11: SumPow[,]) (c12: SumPow[,]) (c21: SumPow[,]) (c22: SumPow[,]) =
                let n = Array2D.length1 c11
                let m = Array2D.length2 c11
                let result = Array2D.init (2 * n) (2 * m) (konst2 (Const Zero))

                for i = 0 to n - 1 do
                    for j = 0 to m - 1 do
                        result.[i, j] <- c11.[i, j]
                        result.[i, j + m] <- c12.[i, j]
                        result.[i + n, j] <- c21.[i, j]
                        result.[i + n, j + m] <- c22.[i, j]

                result

            /// Classic matrix addition.
            let inline private addMatrix (matrix1: SumPow[,]) (matrix2: SumPow[,]) =
                let inline initializer i j = matrix1.[i, j] + matrix2.[i, j]
                Array2D.init (Array2D.length1 matrix1) (Array2D.length2 matrix1) initializer

            /// Classic matrix substraction.
            let inline private subtractMatrix (A: SumPow[,]) (B: SumPow[,]) =
                Array2D.init (Array2D.length1 A) (Array2D.length2 A) (fun i j -> A.[i, j] - B.[i, j])

            /// Classic matrix multiplication for square matrix.
            let inline private multiplyMatrix (A: SumPow[,]) (B: SumPow[,]) (n: int) =
                let result = Array2D.init n n (konst2 (Const Zero))

                for i = 0 to n - 1 do
                    for j = 0 to n - 1 do
                        for k = 0 to n - 1 do
                            result.[i, j] <- result.[i, j] + A.[i, k] * B.[k, j]

                result

            /// The Strassen's multiplication algorithm for square matrix.
            let rec public strassen (A: SumPow[,]) (B: SumPow[,]) =

                // The efficiency of Strassen's algorithm may depend on the processor, but above all on the
                // size of the matrices. It will be less efficient than the naive multiplication algorithm
                // for matrices of modest size.

                if Array2D.length1 A <= 350 then multiplyMatrix A B (Array2D.length1 A) else

                let A11, A12, A21, A22 = splitMatrix A
                let B11, B12, B21, B22 = splitMatrix B

                let taskM1 = Task.Run(fun _ -> strassen (addMatrix A11 A22) (addMatrix B11 B22))
                let taskM2 = Task.Run(fun _ -> strassen (addMatrix A21 A22) B11)
                let taskM3 = Task.Run(fun _ -> strassen A11 (subtractMatrix B12 B22))
                let taskM4 = Task.Run(fun _ -> strassen A22 (subtractMatrix B21 B11))
                let taskM5 = Task.Run(fun _ -> strassen (addMatrix A11 A12) B22)
                let taskM6 = Task.Run(fun _ -> strassen (subtractMatrix A21 A11) (addMatrix B11 B12))
                let taskM7 = Task.Run(fun _ -> strassen (subtractMatrix A12 A22) (addMatrix B21 B22))

                let tasks: Task[] = [| taskM1; taskM2; taskM3; taskM4; taskM5; taskM6; taskM7 |]
                Task.WaitAll tasks

                let M1 = taskM1.Result
                let M2 = taskM2.Result
                let M3 = taskM3.Result
                let M4 = taskM4.Result
                let M5 = taskM5.Result
                let M6 = taskM6.Result
                let M7 = taskM7.Result

                let C11 = addMatrix (subtractMatrix (addMatrix M1 M4) M5) M7
                let C12 = addMatrix M3 M5
                let C21 = addMatrix M2 M4
                let C22 = addMatrix (subtractMatrix (addMatrix M1 M3) M2) M6

                mergeMatrix C11 C12 C21 C22

        module private Operations =

            let public addition (m1: Matrix) (m2: Matrix) =
                let cs1 = copyFreeComponents m1
                let cs2 = copyFreeComponents m2

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
                let cs1 = copyFreeComponents m1
                let cs2 = copyFreeComponents m2

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
                Matrix (Array2D.map (( * ) scalar) (copyFreeComponents m))

            /// Divise each component of the given matrix by the given scalar.
            let public scalarDivision (m: Matrix) (scalar: SumPow) =
                Matrix (Array2D.map (fun c -> c / scalar) (copyFreeComponents m))

            /// A parallelized variant of the classic matrix multiplication. This method is faster for large matrices.
            let private pmultiplication (cs1: SumPow[,]) (cs2: SumPow[,]) (r1: int) (c1: int) (c2: int) =
                let mutable result = Array2D.create r1 c2 (Const Zero)

                [| for i in 0 .. r1 - 1 do
                    for j in 0 .. c2 - 1 do
                        yield
                            Task.Run(fun () ->
                                let mutable sum = Const Zero

                                for k in 0 .. c1 - 1 do
                                    sum <- sum + cs1.[i, k] * cs2.[k, j]

                                result.[i, j] <- sum) |]

                |> Task.WaitAll

                Matrix result

            /// Classic matrix multiplication.
            let public naiveMultiplication (m1: Matrix) (m2: Matrix) =
                let r1, c1 = size m1
                let _, c2 = size m2

                let mutable result = Array2D.create r1 c2 (Const Zero)

                for i in 0 .. r1 - 1 do
                    for j in 0 .. c2 - 1 do
                        for k in 0 .. c1 - 1 do
                            result.[i, j] <- result.[i, j] + m1.[i, k] * m2.[k, j]

                Matrix result

            /// Implement three matrix multiplication algorithms depending of the matrices size.
            let public multiplication (m1: Matrix) (m2: Matrix) =
                let cs1 = copyFreeComponents m1
                let cs2 = copyFreeComponents m2

                let rows1, cols1 = size m1
                let rows2, cols2 = size m2

                if cols1 <> rows2 then
                    raise (IncompatibleMatrixException [ m1; m2 ])

                // For large square matrices, we use the parallelized Strassen algorithm.
                if rows1 >= 500 && isSquareMatrix m1 && isSquareMatrix m2 then
                    let (Matrix m1), (Matrix m2) = m1, m2
                    Matrix (Strassen.strassen m1 m2)

                // For medium matrices that are not square, we use the parallelized version of naive multiplication.
                elif rows1 >= 100 then pmultiplication cs1 cs2 rows1 cols1 cols2

                // In the case of small matrices, we use classical multiplication.
                else naiveMultiplication m1 m2

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
            Matrix (Array2D.map Simplification.fixSimplify (copyFreeComponents m))

        /// Check if the matrix is square.
        let public isSquareMatrix (m: Matrix) =
            let n, m = size m
            n = m

        /// Returns the main diagonal of the given matrix.
        let public diagonal (m: Matrix) =
            if not (isSquareMatrix m) then
                raise (NotASquareMatrixException m)

            let cs = components m

            let l = min (Array2D.length1 cs) (Array2D.length2 cs) - 1
            [| for i in 0 .. l -> cs.[i, i] |]

        /// Generates a square diagonal matrix whose diagonal elements are given in order.
        let public diagonalMatrix (diag: SumPow[]) =
            generate (Array.length diag) (Array.length diag) (fun i j -> if i = j then diag.[i] else Const Zero)

        /// Compute the sum of the diagonal of the given matrix.
        let public trace (m: Matrix) =
            Array.reduce ( + ) (diagonal m)
            |> Simplification.simplify

        /// Use the Laplace expansion method to compute the determinant of the given matrix.
        /// Note: this method is not efficient for large matrix (time complexity: O(n!)).
        /// See https://en.wikipedia.org/wiki/Laplace_expansion.
        let public slowDeterminant (m: Matrix) =
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

            loop (copyFreeComponents m)
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
            let cs1 = copyFreeComponents m1
            let cs2 = copyFreeComponents m2

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
            let cs1 = copyFreeComponents m1
            let cs2 = copyFreeComponents m2

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

            let cs = copyFreeComponents (simplifyComponents m)
            m = idMatrix (Array2D.length1 cs)

        /// Review the submatrix indicated.
        let public subMatrix (matrix: Matrix) (row: int) (col: int) =
            let cs = copyFreeComponents matrix
            let rows = Array2D.length1 cs
            let cols = Array2D.length2 cs

            let mutable sub = Array2D.zeroCreate (rows - 1) (cols - 1)
            
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
            let det = VectorSpaceUtility.fastDeterminant sub
            let sign = if (row + col) % 2 = 0 then 1 else -1
            sign * det

        /// Returns the matrix of co-factors.
        let public cofactorMatrix (matrix: Matrix) =
            if not (isSquareMatrix matrix) then
                raise (NotASquareMatrixException matrix)

            let cs = copyFreeComponents matrix
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

            let cs = copyFreeComponents matrix
            let rows = Array2D.length1 cs
            let cols = Array2D.length2 cs

            let det = VectorSpaceUtility.fastDeterminant matrix
            if not (VectorSpaceUtility.isInvertible matrix) then None else

            let adjoint = adjoint matrix
            let mutable result = Array2D.zeroCreate rows cols

            for i in 0 .. rows - 1 do
                for j in 0 .. cols - 1 do
                    result.[i, j] <- Simplification.simplify (adjoint.[i, j] / det)

            Some (Matrix result)

        /// Returns the QR decomposition of the given matrix (using Gram-Schmidt process).
        /// The matrix Q is an orthogonal and the matrix R is a upper triangular matrix.
        let public qrDecomposition (matrix: Matrix) =
            let m, n = size matrix

            if m < n then
                raise (IncompatibleMatrixException [ matrix ])

            let columns = Array.map Vector (getColumns matrix)
            let normsVs = gramSchmidtNormalized columns
            let Q = fromVectors normsVs
            let f r c = if r <= c then dotProduct normsVs.[r] columns.[c] else Const Zero
            let R = generate n n f
            Q, R

        /// Perform the LU decomposition to the given matrix, and return the resulting matrices L and U.
        /// See https://en.wikipedia.org/wiki/LU_decomposition.
        let public luDecomposition (matrix: Matrix) =
            let n, m = size matrix            
            let mutable L = Array2D.init n n (fun i j -> if i = j then Const One else Const Zero)
            let mutable U = components matrix

            for k in 0 .. n - 1 do
                for i in k + 1 .. n - 1 do
                    let factor = Simplification.simplify (U.[i, k] / U.[k, k])
                    L.[i, k] <- factor
                    for j in k .. m - 1 do
                        U.[i, j] <- Simplification.simplify (U.[i, j] - factor * U.[k, j])

            Matrix L, Matrix U

        /// Returns the characteristic polynomial of the given matrix.
        let public characteristicPolynomial (matrix: Matrix) (variable: SumPow) =
            if not (isSquareMatrix matrix) then
                raise (NotASquareMatrixException matrix)

            // Note: the Faddeev–LeVerrier algorithm is probably better.
            // See https://en.wikipedia.org/wiki/Faddeev%E2%80%93LeVerrier_algorithm.

            let λI = variable * idMatrix (fst (size matrix))
            VectorSpaceUtility.fastDeterminant (matrix - λI)

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
            let cs = copyFreeComponents (transpose matrix)
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

    /// This module covers some other elements of linear algebra.
    module public VectorSpaceUtility =
        open System.Linq
        open Vector
        open Matrix
        open Liyh.Kernel.SumPow.PureConstantExpression

        exception public VectorsDoNotHaveSameDimensionException of Vector seq
        exception public DefectiveMatrixException of Vector seq
        exception public UndefinedSizeForVectorSpaceException of int
        exception public NotABasisException of Vector seq * int
        exception public BadStepInGaussianEliminationException of int * int
        exception public NotRowEchelonFormMatrixException of Matrix
        exception public ViolationOfRankNullityTheoremException of Matrix
        exception public NonIntegerComponentsException of Matrix
        exception public BrokenHermiteNormalFormException of matrix: bigint[,] * q: bigint * r: bigint

        module private RowOperations =

            /// Swap the indicated rows of the given matrix.
            /// Note: the function MODIFIES the given matrix (as a reference) but also returns it.
            let inline public rowSwitching (matrix: _[,]) (r1: int) (r2: int) =
                for col in 0 .. Array2D.length2 matrix - 1 do
                    let tmp = matrix.[r1, col]
                    matrix.[r1, col] <- matrix.[r2, col]
                    matrix.[r2, col] <- tmp

                matrix

            let inline rowReduce (matrix: SumPow[,]) (r1: int) (r2: int) (col: int) =
                let factor = matrix.[r2, col] / matrix.[r1, col]

                for col in col .. Array2D.length2 matrix - 1 do
                    matrix.[r2, col] <- matrix.[r2, col] - factor * matrix.[r1, col]
                                        |> Simplification.simplify

                matrix

            /// Multiply the indicated row of the given matrix by the given scalar.
            /// Note: the function MODIFIES the given matrix (as a reference) but also returns it.
            let inline public rowScaling (matrix: 'a[,]) (r: int) (factor: 'a) =
                for c in 0 .. Array2D.length2 matrix - 1 do
                    matrix.[r, c] <- factor * matrix.[r, c]

                matrix

            /// Sum the indicated row of the given matrix by itself plus the given scalar.
            /// Note: the function MODIFIES the given matrix (as a reference) but also returns it.
            let inline public rowAddition (matrix: 'a[,]) (r: int) (factor: 'a) =
                for c in 0 .. Array2D.length2 matrix - 1 do
                    matrix.[r, c] <- matrix.[r, c] + factor * matrix.[r, c]

                matrix

        /// This function performs a single step of Gaussian elimination. The initial `step` is `(0, 0)` and should not
        /// be different, otherwise the result could be inconsistent. The return value is a tuple containing the new matrix
        /// obtained (it may not change between two steps) and the next `step`, which should be called to perform the next
        /// step of the gaussian elimination if necessary. And so on. For example:
        /// 
        ///     let mutable step = Some (0, 0)
        ///     let mutable prev = initialMatrix
        ///     
        ///     while Option.isSome step do
        ///         let prev', step' = gaussianEliminationStep prev (Option.get step)
        ///         prev <- prev'
        ///         step <- step'
        /// 
        /// When no more steps are possible, the algorithm is finished and the next step is `None`.
        let public gaussianEliminationStep (matrix: Matrix) (step: int * int) =
            let rows, cols = size matrix
            let r, lead = step

            if (r < 0 || lead < 0) || (r > rows || lead > cols) then
                raise (BadStepInGaussianEliminationException step)

            // If the matrix is already in the desired form, then we don't need to continue the algorithm.
            if isRowEchelonForm matrix then (matrix, None) else

            let mutable cs = components matrix

            /// This function returns the return value (since `cs` is modified).
            let inline ret() = simplifyComponents (Matrix cs)

            if r >= rows || lead >= cols then (ret (), None)
            else
                let mutable i = r

                while i < rows && Misc.isZero cs.[i, lead] do
                    i <- i + 1

                if i < rows then
                    cs <- RowOperations.rowSwitching cs i r
                    let pivot = cs.[r, lead]

                    if not (Misc.isZero pivot) then
                        for col in lead .. cols - 1 do
                            cs.[r, col] <- cs.[r, col] / pivot
                                           |> Simplification.simplify

                        for i in 0 .. rows - 1 do
                            if i <> r && not (Misc.isZero cs.[i, lead]) then
                                cs <- RowOperations.rowReduce cs r i lead

                    (ret(), Some (r + 1, lead + 1))
                else
                    (ret(), Some (r, lead + 1))

        /// Checks whether the given matrix is in the row echelon form, i.e. the following properties are required:
        ///     - All rows having only zero entries are at the bottom of the matrix.
        ///     - The left-most nonzero entry of every nonzero row is on the right of the leading entry of every row above.
        let public isRowEchelonForm (matrix: Matrix) =
            let cs = copyFreeComponents matrix
            let rows, cols = size matrix

            /// This function finds the first column with a non-null element in a given row.
            /// If no non-null value is found, it returns `None`.
            let rec findFirstNonZero (row: int) (startCol: int) =
                if startCol >= cols then None
                elif not (Misc.isZero cs.[row, startCol]) then Some startCol
                else findFirstNonZero row (startCol + 1)

            /// This function checks each row of the matrix. It ensures that the pivot of the current row is to the
            /// right of the pivot of the previous row and that all rows after a null row are also null.
            let rec checkRow (currentRow: int) (lastPivotCol: int) =
                if currentRow >= rows then true
                else
                    match findFirstNonZero currentRow 0 with
                    | None ->

                        // In this case, the current row is all zeros.
                        // We ensure all following rows are also all zeros

                        if currentRow = rows - 1 then true
                        else
                            let sbmx = Array2D.map Misc.isZero (Array2D.getSubMatrix cs currentRow 0 1 cols)
                            let allZeros = Array2D.fold ( && ) true sbmx

                            allZeros && checkRow (currentRow + 1) lastPivotCol

                    | Some pivotCol ->
                        if lastPivotCol >= pivotCol then false
                        else checkRow (currentRow + 1) pivotCol

            checkRow 0 -1

        /// Checks whether the transpose of the given matrix is in the row echelon form.
        let public isColumnEchelonForm (matrix: Matrix) =
            isRowEchelonForm (transpose matrix)

        /// Perform the Gaussian elimination to the given matrix, and return the resulting matrix.
        /// See https://en.wikipedia.org/wiki/Gaussian_elimination.
        let public gaussianElimination (matrix: Matrix) =
            let mutable cs = components matrix

            // Row operations:
            //  1. Swap the positions of two rows.
            //  2. Multiply a row by a non-zero scalar.
            //  3. Add to one row a scalar multiple of another.

            let inline reduceRow (matrix: SumPow[,]) (r1: int) (r2: int) (col: int) =
                let factor = matrix.[r2, col] / matrix.[r1, col]

                for col in col .. Array2D.length2 matrix - 1 do
                    matrix.[r2, col] <- matrix.[r2, col] - factor * matrix.[r1, col]
                                        |> Simplification.simplify

                matrix

            let rows, cols = size matrix

            // The tail-recursive function below modifies the `cs` matrix in-place. We use a tail-recursive function
            // because it's more convenient given that F# allow breaing loops.

            let rec processRow r lead =
                if r >= rows || lead >= cols then
                    cs
                else

                    // The naive implementation of the Gaussian elimination is likely to involve divisions by 0 for a
                    // pivot chosen awkwardly, so we make sure that the pivot is non-zero before the reduction.

                    // What's more, F# has no mechanism for breaking loops, the chosen implementation being semi-imperative,
                    // we trick using a while loop and a mutable index.

                    // Note: in literature, the term "pivot" is analogous to "leading value".

                    let mutable i = r

                    while i < rows && Misc.isZero cs.[i, lead] do
                        i <- i + 1

                    if i < rows then
                        cs <- RowOperations.rowSwitching cs i r
                        let pivot = cs.[r, lead]

                        if not (Misc.isZero pivot) then
                            for col in lead .. cols - 1 do
                                cs.[r, col] <- cs.[r, col] / pivot
                                               |> Simplification.simplify

                            for i in 0 .. rows - 1 do
                                if i <> r && not (Misc.isZero cs.[i, lead]) then
                                    cs <- RowOperations.rowReduce cs r i lead //reduceRow cs r i lead

                        processRow (r + 1) (lead + 1)
                    else
                        processRow r (lead + 1)

            cs <- processRow 0 0
            Matrix cs |> simplifyComponents

        /// Compute the rank of the given matrix, i.e. the dimension of the vector space spanned by its columns.
        /// See https://en.wikipedia.org/wiki/Rank_(linear_algebra).
        let public matrixRank (matrix: Matrix) =
            let ge = gaussianElimination matrix
            let rows, cols = size ge

            let mutable result = 0

            for row in 0 .. rows - 1 do
                if Array.exists (not << Misc.isZero) (Array.init cols (fun col -> ge.[row, col])) then
                    result <- result + 1

            result

        /// Compute the nullity of the given matrix, i.e. the number of vectors present in the null space.
        /// See https://en.wikipedia.org/wiki/Rank%E2%80%93nullity_theorem.
        let public matrixNullity (matrix: Matrix) =
            snd (size matrix) - matrixRank matrix

        /// Check that the given vectors are linearly independent.
        let public areLinearlyIndependent (vectors: Vector array) =
            let numOfVectors = Array.length vectors
            let dim = Vector.size (Array.head vectors)

            if not (Array.forall (fun vec -> Vector.size vec = dim) vectors) then
                raise (VectorsDoNotHaveSameDimensionException vectors)

            // 1. If there are as many vectors as their dimension, then we check that the associated determinant is not 0.
            // 2. If there are more vectors than their dimension, then they are necessarily linearly dependent.
            // 3. If there are fewer vectors than their dimension, then we look to see if the rank of the associated matrix
            //    is equal to the number of vectors. If so, then they are linearly independent.

            if   numOfVectors = dim then (not << Misc.isZero) (fastDeterminant (fromVectors vectors))
            elif numOfVectors > dim then false
            else numOfVectors = matrixRank (fromVectors vectors)

        /// Check that the given vectors are linearly dependent.
        let public areLinearlyDependent = not << areLinearlyIndependent

        /// Use the Bareiss algorithm to calculate the determinant of the given matrix.
        /// This need O(n^3) arithmetics operations, while `Matrix.slowDeterminant` need O(n!) ones.
        /// See https://en.wikipedia.org/wiki/Bareiss_algorithm.
        let public fastDeterminant (matrix: Matrix): SumPow =
            if not (isSquareMatrix matrix) then
                raise (NotASquareMatrixException matrix)

            let mutable cs = components matrix
            let dim = Array2D.length1 cs

            // The tail-recursive function below modifies the `cs` matrix in-place. We use a tail-recursive function
            // because it's more convenient given that F# allow breaing loops.

            let rec loop k sign =
                if k = dim - 1 then
                    sign * cs.[dim - 1, dim - 1]

                else if Misc.isZero cs.[k, k] then

                    let rec findPivot m =
                        if m = dim then
                            Const Zero // If no pivot is found, then the determinant is zero.
                        elif not (Misc.isZero cs.[m, k]) then
                            cs <- RowOperations.rowSwitching cs k m
                            loop k -sign
                        else
                            findPivot (m + 1)

                    findPivot (k + 1)
                else
                    for i in k + 1 .. dim - 1 do
                        for j in k + 1 .. dim - 1 do
                            cs.[i, j] <- cs.[k, k] * cs.[i, j] - cs.[i, k] * cs.[k, j]

                            if k <> 0 then
                                cs.[i, j] <- cs.[i, j] / cs.[k - 1, k - 1]

                    loop (k + 1) sign

            loop 0 1 |> Simplification.simplify

        /// Use the Faddeev–LeVerrier algorithm to calculate the characteristic polynomial of the given matrix.
        /// See https://en.wikipedia.org/wiki/Faddeev%E2%80%93LeVerrier_algorithm.
        let public fastCharacteristicPolynomial (matrix: Matrix) (variable: SumPow) =
            if not (isSquareMatrix matrix) then
                raise (NotASquareMatrixException matrix)

            let n, _ = size matrix
            let mutable akMat = components matrix
            let mutable result = Array.init (n + 1) (konst (Const One))

            for k in 1 .. n do
                let ak = - trace (Matrix akMat) / k
                result.[k] <- ak
                akMat <- components (Matrix akMat + diagonalMatrix [| for _ in 1 .. n -> ak |])
                akMat <- components (matrix * Matrix akMat)

            Polynomial.Convertion.fromCoefficients [ variable ] [ n ] (List.ofArray result)

        /// Check that the given family of vectors "forms a basis" for a n-vector space.
        /// Note: In fact, it doesn't make much sense to say that "a family of vectors forms a basis" without specifying
        /// over which field, we assume that the user knows what he or she is doing (SumPow is a particular space).
        let public isBasis (vectors: Vector array) (spaceDim: int) =
            if spaceDim <= 0 then
                raise (UndefinedSizeForVectorSpaceException spaceDim)

            // In the absence of knowing whether the vector family "spans" we simply check
            // that the dimension of the basis corresponds to that of the vector space.

            Array.length vectors = spaceDim && areLinearlyIndependent vectors

        let public jordanMatrix (matrix: Matrix) =
            // https://empslocal.ex.ac.uk/people/staff/rjchapma/courses/jcf.pdf
            ()

        /// Performs a basis change on the given basis given a basis change matrix.
        let public changeBasis (basis: Vector array) (cobMatrix: Matrix) =
            if not (isSquareMatrix cobMatrix) then
                raise (NotASquareMatrixException cobMatrix)

            let dim, _ = size cobMatrix
            if not (isBasis basis dim) then
                raise (NotABasisException (basis, dim))

            let inline mapper vec =
                let cv = fromVector vec Matrix1D.ColumnVector
                let rs = cobMatrix * cv
                let cs = Array2D.column 0 (components rs)

                fromSeq cs

            Array.map mapper basis

        /// Append the given column to the given matrix on the right.
        let public augmentedMatrix (matrix: Matrix) (column: Vector) =
            let rows, cols = size matrix

            if Vector.size column <> rows then
                raise (IncompatibleMatrixException [ matrix; fromVector column Matrix1D.ColumnVector ])

            let inline initializer i j =
                if j < cols then matrix.[i, j] else column.[i]

            Matrix (Array2D.init rows (cols + 1) initializer)

        /// Given a matrix in row echelon form, identify the columns for which there is no pivot (the free columns).
        let private freeColumns (matrix: Matrix) =
            if not (isRowEchelonForm matrix) then
                raise (NotRowEchelonFormMatrixException matrix)

            let m, n = size matrix

            // Contains information about whether a column is a free column or not.
            let mutable pivotColumns = Array.init n (konst false)

            for i in 0 .. m - 1 do
                let mutable foundPivot = false

                for j in 0 .. n - 1 do
                    if
                        not foundPivot
                        && Misc.isOne matrix.[i, j]
                        && Array.forall Misc.isZero
                            [| for k in 0 .. m - 1 -> if k <> i then matrix.[k, j] else Const Zero |]
                    then
                        pivotColumns.[j] <- true
                        foundPivot <- true

            [| for j in 0 .. n - 1 do
                if not pivotColumns.[j] then
                    yield j |]

        /// Compute a basis of the kernel of the given matrix.
        /// See https://en.wikipedia.org/wiki/Kernel_(linear_algebra).
        let public kernelBasis (matrix: Matrix) =
            let mref = gaussianElimination matrix
            let rows, cols = size mref

            // The algorithm works as follows: we calculate the row echelon form of the matrix, which gives us access 
            // to the free variables and the lined variables (or, equivalently in our case, the free and non-free columns).
            // The non-free variables are the ‘pivots’ and all we have to do is solve the associated equations to obtain
            // the components of the base vectors.
            // For better explanation, see
            //  - https://math.stackexchange.com/questions/88301/finding-the-basis-of-a-null-space
            //  - https://people.math.carleton.ca/~kcheung/math/books/manuel-AL/fr/retour-sur-le-noyau-dune-matrice.html

            let pivots = // Search for columns with pivot points
                Array.init cols
                    (fun j -> Array.tryFindIndex (fun i -> Misc.isOne mref.[i, j]) [| 0 .. rows - 1 |])

            let inline initializer freeCol i =
                if i = freeCol then Const One
                elif i > freeCol then Const Zero
                else match pivots.[i] with
                     | Some r -> -mref.[r, freeCol]
                     | None -> Const Zero

            let inline mapper freeCol =
                Array.init cols (initializer freeCol)

            // The dimension of the kernel corresponds to the number of free variables (~columns)
            // according to the Rank–nullity theorem. https://en.wikipedia.org/wiki/Rank%E2%80%93nullity_theorem

            let freeVariables = freeColumns mref
            if matrixNullity matrix <> Array.length freeVariables then
                raise (ViolationOfRankNullityTheoremException matrix)

            Array.map (mapper >> Vector) freeVariables

        /// Compute a basis of the image of the given matrix.
        /// See https://en.wikipedia.org/wiki/Row_and_column_spaces.
        let public imageBasis (matrix: Matrix) =
            let mref = gaussianElimination (transpose matrix)
            Array.filter (fun (a: _ array) -> a.Any (not << Misc.isZero)) (getRows mref)

        /// Check whether the given vectors form a basis of the given matrix.
        let public isKernelBasis (vectors: Vector array) (matrix: Matrix) =
            isBasis vectors (matrixNullity matrix)

        /// Check whether the given matrix has an inverse.
        let public isInvertible (matrix: Matrix) =
            let result = isSquareMatrix matrix && matrixRank matrix = fst (size matrix)
            #if DEBUG // Gaussian elimination can lead to heavy calculations that
                      // are not always simplified by SumPow...
                      // In debug mode, a double check is performed.
            if not (Misc.isZero (fastDeterminant matrix)) <> result then
                failwithf "Incompatible results: %A" matrix
            result
            #else
            result
            #endif

        /// Returns the Hermite normal form of the given integer non-singular m×n matrix, as well as the unimodular
        /// square matrix of the elementary operations. The algorithm used is based on the Gaussian elimination algorithm,
        /// it follow the same principle, but restricted to Z rather than Q.
        /// 
        /// Implementation follows the steps from Lattice "Basis Reduction An Introduction to the LLL Algorithm and Its
        /// Applications" By Murray R. Bremner (2012) p. 228.
        let internal hermiteNormalForm' (matrix: bigint[,]) =
            let m = Array2D.length1 matrix
            let n = Array2D.length2 matrix

            let mutable H = Array2D.copy matrix
            let mutable U = Array2D.init m m (fun i j -> if i = j then 1I else 0I)

            let inline reduce i j k =
                let q, r = H.[k, j] / H.[i, j], H.[k, j] % H.[i, j]

                // The integers q and r are such that Hₖⱼ = qHᵢⱼ + r.
                if (H.[k, j] <> q * H.[i, j] + r) then
                    raise (BrokenHermiteNormalFormException (matrix, q, r))

                if q <> 0 then
                    H.[k, *] <- Array.map2 (fun a b -> a - q * b) H.[k, *] H.[i, *]
                    U.[k, *] <- Array.map2 (fun a b -> a - q * b) U.[k, *] U.[i, *]

            let mutable i, j = 0, 0

            while i <= m - 1 && j <= n - 1 do
                if Array.forall (( = ) 0I) [| for k = i to m - 1 do H.[k, j] |] then
                    j <- j + 1
                else
                    while not (H.[i, j] > 0I && Array.forall (fun k -> H.[k, j] = 0) [| i + 1 .. m - 1 |]) do

                        // let k = 
                        //     [| i .. m - 1 |]
                        //     |> Array.filter (fun k -> H.[k, j] <> 0I)
                        //     |> Array.minBy (fun k -> abs H.[k, j])

                        let k = 
                            [| i .. m - 1 |]
                            |> Array.fold (fun acc k -> 
                                if H.[k, j] <> 0I then 
                                    match acc with
                                    | -1 -> k
                                    | minK when abs H.[k, j] < abs H.[minK, j] -> k
                                    | _ -> acc
                                else acc) -1

                        if i <> k then
                            H <- RowOperations.rowSwitching H i k
                            U <- RowOperations.rowSwitching U i k

                        if H.[i, j] < 0 then
                            H.[i, *] <- Array.map (( * ) -1I) H.[i, *]
                            U.[i, *] <- Array.map (( * ) -1I) U.[i, *]

                        for k in i + 1 .. m - 1 do
                            reduce i j k

                    for k in 0 .. i - 1 do
                        reduce i j k

                    i <- i + 1
                    j <- j + 1

            (H, U)

        /// Returns the Hermite normal form of the given integer non-singular m×n matrix, as well as the unimodular
        /// square matrix of the elementary operations. The algorithm used is based on the Gaussian elimination algorithm,
        /// it follow the same principle, but restricted to Z rather than Q.
        /// 
        /// Implementation follows the steps from Lattice "Basis Reduction An Introduction to the LLL Algorithm and Its
        /// Applications" By Murray R. Bremner (2012) p. 228.
        let public hermiteNormalForm (matrix: Matrix) =
            if not (isInvertible matrix) then
                raise (SingularMatrixException matrix)
            
            let components = copyFreeComponents matrix

            if not (Array2D.forall Misc.isPureConstInteger components) then
                raise (NonIntegerComponentsException matrix)

            let intMatrix = Array2D.map (function PureConstantExpressionInteger n -> bigint n) components
            let H, U = hermiteNormalForm' intMatrix

            let H = Array2D.map (fromBigInt >> Const) H
            let U = Array2D.map (fromBigInt >> Const) U

            (H, U)

