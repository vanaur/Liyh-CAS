namespace Liyh.Utils

#nowarn "9"

[<AutoOpen>]
module rec Utils =
    open System
    open System.Linq
    open System.Collections.Generic
    open System.Runtime.CompilerServices

    /// Used to store the results of a (pure) function so that they have not to be recalculated later in a re-call.
    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let inline public memoize ([<InlineIfLambda>] fn: 'a -> 'b) =
        let cache = new Dictionary<'a, 'b>()

        fun arg ->
            match cache.TryGetValue arg with
            | true, value -> value
            | _ ->
                let value = fn arg
                cache.Add(arg, value) |> ignore
                value

    /// Generates a hash code regardless of the order of the elements in the given sequence.
    [<MethodImpl(MethodImplOptions.AggressiveOptimization)>]
    let inline public commutativeHash (xs: 'a list) ([<InlineIfLambda>] hash: 'a -> int) =
        match xs with
        | [] -> 7307
        | [ x ] -> hash x
        | xs -> List.fold (fun acc x -> Operators.(+) acc (hash x)) 7307 xs

    // Some extensions to the standard module.
    module public Array =

        /// Builds an array from the given list (faster than in the standard library).
        let public ofList' (lst: 'T list) =
            List.toArray lst

    // Some extensions to the standard module.
    module public Array2D =
        /// Obtains the row `i` of the given 2D array.
        let inline public row i (table: 'T[,]) = table.[i, *] |> Seq.cast<'T>

        /// Obtains the column `i` of the given 2D array.
        let inline public column i (table: 'T[,]) = table.[*, i] |> Seq.cast<'T>

        /// Tests if all elements of the collection satisfy the given predicate.
        let public forall (predicate: 't -> bool) (matrix: 't[,]) =
            let mutable running1 = true
            let mutable result = true

            let mutable i, j = 0, 0
            
            while running1 do
                let mutable running2 = running1

                while running2 do
                    if not (predicate matrix.[i, j]) then
                        running1 <- false
                        running2 <- false
                        result <- false
                    else
                        if j = Array2D.length2 matrix then
                            running2 <- false
                            j <- 0
                        else
                            j <- j + 1

                if i = Array2D.length1 matrix then
                    running1 <- false
                    i <- 0
                else
                    i <- i + 1

            result

        /// Applies a function to each element of the collection, threading an accumulator argument through the computation.
        let public foldi (folder: int -> int -> 'State -> 'T -> 'State) (state: 'State) (array: 'T[,]) =
            let mutable result = state

            for x in 0 .. Array2D.length1 array - 1 do
                for y in 0 .. Array2D.length2 array - 1 do
                    result <- folder x y result (array.[x, y])

            result
        
        /// Applies a function to each element of the collection, threading an accumulator argument through the computation.
        let public fold (folder: 'State -> 'T -> 'State) (state: 'State) (array: 'T[,]) =
            foldi (fun _ _ -> folder) state array

        /// Extracts a submatrix from the given 2D matrix, specifying the starting row and column and the
        /// number of rows and columns to extract.
        let public getSubMatrix (matrix: 'a [,]) (startRow: int) (startCol: int) (numRows: int) (numCols: int) : 'a[,] =
            let mutable result = Array2D.zeroCreate<'a> numRows numCols

            for i in 0 .. numRows - 1 do
                for j in 0 .. numCols - 1 do
                    result.[i, j] <- matrix.[startRow + i, startCol + j]

            result

    [<AutoOpen>]
    module public Functional =

        let inline public uncurry ([<InlineIfLambda>] f) (a, b) = f a b
        let inline public curry ([<InlineIfLambda>] f) a b = f (a, b)
        let inline public flip ([<InlineIfLambda>] f) a b = f b a
        let inline public tuple2 a b = a, b
        let inline public konst x _ = x
        let inline public konst2 x _ _ = x

    /// Given a function `f` and an argument `x`, the ‘fixed point’ is defined as the value `f(x)` such that `f(f(x)) = f(x)`.
    /// In other words, the fixed point consists of applying a function to a result until the result no longer changes. This
    /// is used in particular in simplifications, where a simplification function may not simplify all at once, but needs
    /// several iterations. It is possible that the fixed point is not found and that the function runs to infinity (generally
    /// a sign of an error in the implementation of `f` or of a comparison `=` that is not powerful enough).
    /// In this case, "maximum fixed-point" are also provided.
    module public FixedPoint =
        exception public MaximumAuthorisedFixedPointReachedException of int

        /// Same as `fixedPoint` but return the number of iterations done until the fixed point
        /// has been reached.
        let inline public fixedPointCount f x =
            let rec fp f x count =
                let r = f x in if x = r then (x, count) else fp f r (count + 1)

            fp f x 0

        /// Fixed point for debug, that print the number of loops done.
        let inline public fixedPointDebug f x =
            let result, count = fixedPointCount f x
            printfn "[debug | fixed point]: %d" count
            result

        /// Same as `fixedPoint` but require a maximum looping point to prevent infinite or too deep looping.
        /// No exception is thrown if the maximum recursion point is reached.
        let inline public fixedPointMax max f x =
            let rec fp f x =
                function
                | count when count >= max -> (count, x)
                | count -> let r = f x in if x = r then (count, r) else fp f r (count + 1)

            fp f x 0

        /// Same as `fixedPointMax` but don't return the number of iterations.
        let inline public fixedPointMax' max f x =
            snd (fixedPointMax max f x)

        /// Apply the function `f` to the given argument as many times as necessary so that the result found no longer
        /// changes after applying `f` once more. This function can loop infinitely.
        let rec public fixedPoint f x =
            let r = f x in if x = r then x else fixedPoint f r

        /// Same as `fixedPointMax` but will raise an exception if a maximum point is reached.
        let inline public tryFixedPoint max f x =
            let count, result = fixedPointMax max f x

            if count >= max then
                raise (MaximumAuthorisedFixedPointReachedException max)
            else
                result

    // Some extensions to the standard module.
    [<AutoOpen>]
    module public Math =
        open System.Numerics

        exception public IntegerSquareRootOfNegativeNumberException of int
        exception public NegativeFactorialException of int
        exception public BadStirlingKindException of int

        /// Returns the quotient and the remainder of the division.
        let inline public divRem (a: int) (b: int) =
            (a / b), (a % b)

        /// Calculates the GCD of `a` and `b`, big integers.
        let inline public bigintGCD a b =
            Numerics.BigInteger.GreatestCommonDivisor(a, b)

        /// Calculates the GCD of `a` and `b`, integers.
        let inline public intGCD a b =
            let rec gcd a b = if b = 0 then a else gcd b (a % b) in gcd a b

        /// Calculates the GCD of `a` and `b`, doubles.
        let inline public doubleGCD a b =
            let rec gcd a b = if b = 0. then a else gcd b (a % b) in gcd a b

        /// Calculates the LCM of `a` and `b`, big integers.
        let inline public bigintLCM a b = a * b / bigintGCD a b

        /// Calculates the LCM of `a` and `b`, big integers.
        let inline public intLCM a b = a * b / intGCD a b

        /// Calculates the LCM of `a` and `b`, big integers.
        let inline public doubleLCM a b = a * b / doubleGCD a b

        /// Calculates the binomial coefficient (n k).
        /// See https://en.wikipedia.org/wiki/Binomial_coefficient.
        let inline binomial n k =
            List.fold (fun s i -> s * (n - i + 1) / i) 1 [ 1..k ]

        /// Calculates the binomial coefficient (n k).
        /// See https://en.wikipedia.org/wiki/Binomial_coefficient.
        let inline fbinomial (n: double) (k: double) =
            Array.fold (fun s i -> s * (n - i + 1.0) / i) 1.0 [| 1.0 .. k |]

        /// Calculates the binomial coefficient (n k).
        /// See https://en.wikipedia.org/wiki/Binomial_coefficient.
        let inline dbinomial (n: decimal) (k: decimal) =
            Array.fold (fun s i -> s * (n - i + 1m) / i) 1m [| 1m .. k |]

        /// Calculates the binomial coefficient (n k).
        /// See https://en.wikipedia.org/wiki/Binomial_coefficient.
        let inline ibinomial (n: bigint) (k: bigint) =
            Array.fold (fun s i -> s * (n - i + 1I) / i) 1I [| 1I .. k |]

        /// Calculates the multinomial coefficient.
        /// See https://en.wikipedia.org/wiki/Multinomial_theorem.
        let public multinomial (numbers: int list) =
            let mutable logarithms = List<double>()
            let mutable sum = 0.

            for k = 2 to List.sum numbers do
                if k - 2 < logarithms.Count then
                    sum <- sum + logarithms.[k - 2]
                else
                    let lg = log (double k)
                    logarithms.Add lg
                    sum <- sum + lg

            for number in numbers do
                for k = 2 to number do
                    sum <- sum - logarithms.[k - 2]

            (round >> int) (exp sum)

        /// Calculate the square root of the given integer as an integer.
        let inline isqrt (n: int) =
            if n < 0 then
                raise (IntegerSquareRootOfNegativeNumberException n)

            let rec loop x y =
                if x > y then
                    let x' = (x + y) / 2
                    loop x' (n / x')
                else
                    x

            loop n 1

        /// Returns the number of digits that make up the given integer.
        let public digitCount number =
            if number < 10 then 1 else int (floor (BigInteger.Log10 number + 1.))

        /// Returns the number of digits that make up the given integer.
        let public digitCountBigInt number =
            if number < 10I then 1 else int (floor (BigInteger.Log10 number + 1.))

        /// Count the number of decimal places the value has.
        let public decimalCount (value: double) =
            if value = 0.0 then 0 else

            let rec countDecimalsHelper (value: double) (count: int) =
                let fraction = value - Math.Floor(value)
                if fraction = 0.0 then count
                else
                    let newValue = fraction * 10.0
                    countDecimalsHelper newValue (count + 1)

            countDecimalsHelper value 0

        /// Determine whether the two floats are equal to the given precision.  If `eps` is `None` then the
        /// comparison is made with a fixed femto-precision (`1e-15`).
        let inline public approximatelyEquals (a: double) (b: double) (eps: double voption) =
            abs (a - b) < if eps.IsNone then 1e-14 else eps.Value

        /// Returns the generic n-Cartesian product of the given list.
        let public cartProd lists =
            let inline inner xs ys =
                [ for x in xs do
                      for y in ys -> x :: y ]

            List.foldBack inner lists [ [] ]

        /// Recursive Cooley–Tukey fast Fourier transform.
        let public fft (lst: Complex list) =

            let inline fac k n =
                let m2pi = -4. * acos 0.
                Complex.FromPolarCoordinates(1., m2pi * float k / float n)

            let inline merge l r n =
                let f (k, t) x = (k + 1, (fac k n) * x :: t)
                let z = List.rev (snd (List.fold f (0, []) r))
                List.map2 ( + ) l z @ List.map2 ( - ) l z

            let rec ditfft2 a n s =
                if n = 1 then
                    [ List.item a lst ]
                else
                    let odd = ditfft2 a (n / 2) (2 * s)
                    let even = ditfft2 (a + s) (n / 2) (2 * s)
                    merge odd even n

            ditfft2 0 (List.length lst) 1

        /// Calculate the natural factorial of the given number.
        let inline public ifactorial (n: int) =
            if n < 0 then
                raise (NegativeFactorialException n)

            let rec loop result n =
                if n <= 1 then result
                else loop (result * bigint n) (n - 1)

            loop 1I n

        /// Calculate the first or second kind Stirling number.
        /// See https://en.wikipedia.org/wiki/Stirling_number#Notation.
        let private stirling (kind: int) (n: int) (k: int) =
            if kind <> 1 && kind <> 2 then
                raise (BadStirlingKindException kind)

            let mutable temp = Array2D.zeroCreate (n + 1) (k + 1)
            temp.[0, 0] <- 1I

            for i in 1 .. n do
                for j in 1 .. min i k do
                    let kfactor = if kind = 1 then (i - 1) else (j - 0)
                    temp.[i, j] <- temp.[i - 1, j - 1] + bigint kfactor * temp.[i - 1, j]

            temp.[n, k]

        /// Calculate the first kind Stirling number.
        /// See https://en.wikipedia.org/wiki/Stirling_numbers_of_the_first_kind.
        let public stirling1 =
            stirling 1

        /// Calculate the second kind Stirling number.
        /// See https://en.wikipedia.org/wiki/Stirling_numbers_of_the_second_kind.
        let public stirling2 =
            stirling 2

        /// Compute each permutation of the given items.
        let rec public permutations =
            function
            | [] -> seq [List.empty]
            | x :: xs -> Seq.collect (insertions x) (permutations xs)

        and private insertions x =
            function
            | [] -> [[x]]
            | (y :: ys) as xs -> (x :: xs) :: (List.map (fun x -> y :: x) (insertions x ys))

        /// Implement the extended euclidean algorithm (extended GCD) for integers.
        /// The return value is the tuple `(d, u, v)` such that `au + bv = d`.
        let rec egcd (a: bigint) (b: bigint) =
            if b = 0I then (a, 1I, 0I)
            else
                let (d', u', v') = egcd b (a % b)
                (d', v', u' - (a / b) * v')

    // Some extensions to the standard module.
    module public List =

        /// Increments a counter for each element in the list that checks the given predicate.
        let inline public countWhen ([<InlineIfLambda>] f: 't -> bool) (xs: 't list) =
            xs.Count f

        /// Applies an accumulator function over the given list.
        let inline public aggregate ([<InlineIfLambda>] f: 't -> 't -> 't) (xs: 't list) =
            xs.Aggregate f

        /// Flatten the given list of list to a list.
        let inline public flatten (xs: 't list list) =
            List.foldBack ( @ ) xs []

        /// Check that the two given lists are the same up to the their order.
        let inline public areEquivalent xs ys =
            commutativeHash xs hash = commutativeHash ys hash

        /// Checks whether the list contains at least one element verifying the given predicate.
        let inline public containsBy ([<InlineIfLambdaAttribute>] pred: 't -> bool) (lst: 't list) =
            List.tryFind pred lst |> Option.isSome

        /// Pairs each element in the list, if the list contains an odd number of elements then the function asks for the
        /// default element to be paired with the first element.
        let inline public byPair (headDefaultIfOdd: 't) (xs: 't list) =
            (List.chunkBySize 2 >> List.collect List.pairwise) (if List.length xs % 2 <> 0 then headDefaultIfOdd :: xs else xs)

        /// Applies `List.mapi` to the reversed given list.
        let inline public mapiBack ([<InlineIfLambda>] f: int -> 't -> 'u) (xs: 't list) =
            List.mapi f (List.rev xs)

        /// Checks whether the list contains a single element.
        let inline public isSingleton (xs: 't list) =
            List.length xs = 1

        /// Cacat the two lists by deleting the duplicated items.
        let inline public merge xs ys =
            List.distinct (List.append xs ys)

        /// Determines whether any element of the given list satisfies the given predicate.
        let inline public any (xs: 't list) ([<InlineIfLambda>] f: 't -> bool) =
            xs.Any f

        /// Like `List.fold` but adds an argument to the function which gives access to the
        /// next element in the list without consuming it.
        let inline public peekFold (f: 'State -> 'T -> 'T option -> 'State) (state: 'State) (list: 'T list) : 'State =
            let rec loop (s: 'State) (xs: 'T list) =
                match xs, List.tryHead (if List.isEmpty xs then [] else List.tail xs) with
                | [], _ -> s
                | y :: ys, p -> loop (f s y p) ys

            loop state list

        /// Like `peekFold` but adds an argument to the function which gives access to the
        /// previous element in the list without consuming it.
        let public lastAndPeekFold (f: 'State -> 'T option -> 'T -> 'T option -> 'State) (state: 'State) (list: 'T list) =
            let mutable state = state
            let len = List.length list - 1

            for i = 0 to len do
                let last = if i - 1 < 0 || i > len then None else Some list.[i - 1]
                let curr = list.[i]
                let peek = if i + 1 > len then None else Some list.[i + 1]
                state <- f state last curr peek

            state

        /// Computes `f a.[0] + f a.[1] + ... + f a.[n]` where `+` is `g`.
        let inline public foldmap ([<InlineIfLambda>] g) ([<InlineIfLambda>] f) list =

            let rec inner acc i =
                if i >= Seq.length list then acc
                else inner (g acc (f Seq.item i list)) (i + 1)

            inner (f Seq.item 0 list) 1

        /// Executes a fold operation within a list passing as parameter of the folder function the zero based index of each element.
        let inline public foldi ([<InlineIfLambda>] f) state list =
            Seq.fold (fun (prev, i) c -> (f i prev c, i + 1)) (state, 0) list

        /// Remove the first element in the list which satisfies the given predicate.
        let rec public remove pred =
            function
            | x :: xs when pred x -> xs
            | x :: xs -> x :: remove pred xs
            | _ -> []

        /// Remove all the elements in the list which satisfy the given predicate.
        let rec public removeMany pred =
            function
            | x :: xs when pred x -> removeMany pred xs
            | x :: xs -> x :: removeMany pred xs
            | _ -> []

        /// Flatten a list of tuples.
        let inline public flattenTupleList (list: ('a * 'a) list) =
            List.fold (fun acc (x, y) -> x :: y :: acc) [] list

        /// Builds an array from the given list (faster than in the standard library).
        let public toArray (lst: 'T list) =
            let result = Array.zeroCreate (List.length lst)

            let rec loop i =
                function
                | [] -> ()
                | x :: y :: t ->
                    result.[i] <- x
                    result.[i + 1] <- y
                    loop (i + 2) t

                | x :: t ->
                    result.[i] <- x
                    loop (i + 1) t

            result

    // Some extensions to the standard module.
    module public Map =
        exception public UpdatingNonExistentKeyException

        /// Returns a new map whose value stored under the key has been modified to `value`.
        /// This assumes that the key is contained in the map.
        let inline public update map key value =
            if not (Map.containsKey key map) then
                raise UpdatingNonExistentKeyException

            Map.change key (function _ -> Some value) map

        /// Returns a new map whose keys/values are the result of merging `map1` and `map2` according
        /// to a collision handling function `f`.
        let inline public join (map1: Map<'a, 'b>) (map2: Map<'a, 'b>) ([<InlineIfLambda>] f: 'a -> 'b -> 'b -> 'b) =

            let inline inner acc key value =
                match Map.tryFind key acc with
                | Some value' -> Map.add key (f key value value') acc
                | None -> Map.add key value acc

            Map.fold inner map1 map2

        /// Applies a mapping function for each pair of key and value in the given Map.
        let inline public mapKeyValue (mapping: 'a * 'b -> 'a * 'b) (map: Map<'a, 'b>) =
            Map.toArray map |> Array.map mapping |> Map.ofArray

        /// Adds a key/value pair to the Map and, if the key already exists, updates the associated value
        /// via the given updating function.
        let inline public addOrUpdate key value table updating =
            match Map.tryFind key table with
            | None -> Map.add key value table
            | Some oldValue -> update table key (updating oldValue)

        /// Define a one-element Map.
        let inline public singleton key value =
            Map.ofList [ key, value ]

    module public Option =

        /// If the predicate is true for the given value, then return `Some(value)` otherwise return `None`.
        let inline public ofBool (value: 'a) ([<InlineIfLambda>] pred: 'a -> bool) =
            if pred value then Some value else None

    module Dictionary =

        /// Adds a key/value pair to the Dictionary and, if the key already exists, updates the associated value
        /// via the given updating function.
        let inline public addOrUpdate (key: 'Key) (value: 'Value) (table: Dictionary<'Key, 'Value>) (updating: 'Value -> 'Value) =
            if not (table.TryAdd(key, value)) then table.[key] <- updating table.[key]

        /// Folds over the bindings in the dictionary.
        let inline public fold (folder: ('State -> 'Key -> 'T -> 'State)) (state: 'State) (table: Dictionary<'Key, 'T>) =
            let mutable result = state

            for KeyValue(key, value) in table do
                result <- folder result key value

            result

