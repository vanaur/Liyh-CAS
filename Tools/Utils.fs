namespace Liyh.Utils

#nowarn "9"

[<AutoOpen>]
module rec Utils =
    open System
    open System.Linq
    open FSharp.Collections.ParallelSeq
    open System.Collections.Generic
    open System.Collections.Concurrent
    open System.Runtime.CompilerServices

    module Array2D =
        let inline public row i (table: 'T[,]) = table.[i..i, *] |> Seq.cast<'T>
        let inline public column i (table: 'T[,]) = table.[*, i..i] |> Seq.cast<'T>

    let inline public uncurry ([<InlineIfLambda>] f) (a, b) = f a b
    let inline public curry ([<InlineIfLambda>] f) a b = f (a, b)
    let inline public flip ([<InlineIfLambda>] f) a b = f b a

    let inline tuple2 a b = a, b

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
        let inline public fixedPointMax max f x =
            let rec fp f x =
                function
                | count when count >= max -> (count, x)
                | count -> let r = f x in if x = r then (count, r) else fp f r (count + 1)

            fp f x 0

        /// Apply the `f` function to the given argument as many times as necessary so that the result
        /// found no longer changes after applying `f` once more. This function is particularly useful
        /// for algebraic simplification functions.
        let rec public fixedPoint f x =
            let r = f x in if x = r then x else fixedPoint f r

        /// Same as `fixedPointMax` but will raise an exception if a maximum point is reached.
        let inline public tryFixedPoint max f x =
            let count, result = fixedPointMax max f x

            if count >= max then
                raise (MaximumAuthorisedFixedPointReachedException max)
            else
                result

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

    let inline public (@@) (xs: 'a list) (x: 'a) = xs @ [ x ]

    let inline public konst x _ = x
    let inline public konst2 x _ _ = x

    /// Like `List.fold` but adds an argument to the function which gives access to the
    /// next element in the list without consuming it.
    let inline public peekFold (f: 'State -> 'T -> 'T option -> 'State) (state: 'State) (list: 'T list) : 'State =
        let rec loop (s: 'State) (xs: 'T list) =
            match xs, List.tryHead (if List.isEmpty xs then [] else List.tail xs) with
            | [], _ -> s
            | y :: ys, p -> loop (f s y p) ys

        loop state list

    let public lastAndPeekFold
        (f: 'State -> 'T option -> 'T -> 'T option -> 'State)
        (state: 'State)
        (list: 'T list)
        : 'State =
        let mutable state = state
        let len = List.length list - 1

        for i = 0 to len do
            let last = if i - 1 < 0 || i > len then None else Some list.[i - 1]
            let curr = list.[i]
            let peek = if i + 1 > len then None else Some list.[i + 1]
            state <- f state last curr peek

        state

    /// Computes `f a.[0] + f a.[1] + ... + f a.[n]` where `+` is `g`.
    let public foldmap g f list =

        let rec inner acc i =
            if i >= Seq.length list then
                acc
            else
                inner (g acc (f Seq.item i list)) (i + 1)

        inner (f Seq.item 0 list) 1

    /// Executes a fold operation within a list passing as parameter of the folder function
    /// the zero based index of each element.
    let public foldi f state list =
        Seq.fold (fun (prev, i) c -> (f i prev c, i + 1)) (state, 0) list

    let public foldmapRange g f (a, b) =

        let rec inner acc n =
            let n = n + 1

            if n > b then acc else inner (g acc (f n)) n

        inner (f a) a

    let public foldRange f init (a, b) =

        let rec inner acc n =
            if n > b then acc else inner (f acc n) (n + 1)

        inner init a

    let inline public bigintGCD a b =
        Numerics.BigInteger.GreatestCommonDivisor(a, b)

    let inline public intGCD a b =
        let rec gcd a b = if b = 0 then a else gcd b (a % b) in gcd a b

    let inline public doubleGCD a b =
        let rec gcd a b = if b = 0. then a else gcd b (a % b) in gcd a b

    let inline public bigintLCM a b = a * b / bigintGCD a b
    let inline public intLCM a b = a * b / intGCD a b
    let inline public doubleLCM a b = a * b / doubleGCD a b

    let inline public GCD (xs: bigint seq) = xs.Aggregate bigintGCD
    let inline public LCM (xs: bigint seq) = xs.Aggregate bigintLCM

    let inline binomial n k =
        List.fold (fun s i -> s * (n - i + 1) / i) 1 [ 1..k ]

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

    module List =
        let inline public countWhen ([<InlineIfLambda>] f: 't -> bool) (xs: 't list) = xs.Count f
        let inline public aggregate ([<InlineIfLambda>] f: 't -> 't -> 't) (xs: 't list) = xs.Aggregate f
        let inline public flatten (xs: 't list list) = List.foldBack (@) xs []

        let inline public areEquivalent xs ys =
            commutativeHash xs hash = commutativeHash ys hash //xs.OrderBy(id).SequenceEqual(ys.OrderBy id)

        let inline public create ([<InlineIfLambda>] pred: int -> 'a) (size: int) =
            [ for k = 0 to size do
                  pred k ]

        let inline public containsBy ([<InlineIfLambdaAttribute>] pred: 't -> bool) (lst: 't list) =
            List.tryFind pred lst |> Option.isSome

        let inline public byPair (headDefaultIfOdd: 't) (xs: 't list) =
            (List.chunkBySize 2 >> List.collect List.pairwise) (
                if List.length xs % 2 <> 0 then
                    headDefaultIfOdd :: xs
                else
                    xs
            )

        let inline public mapiBack ([<InlineIfLambda>] f: int -> 't -> 'u) (xs: 't list) = List.mapi f (List.rev xs)
        let inline public isSingleton (xs: 't list) = List.length xs = 1
        let inline public merge xs ys = List.append xs ys |> List.distinct
        let inline public any (xs: 't list) (f: 't -> bool) = xs.Any f

        let rec public remove pred =
            function
            | x :: xs when pred x -> xs
            | x :: xs -> x :: remove pred xs
            | _ -> []

        let rec public removeMany pred =
            function
            | x :: xs when pred x -> removeMany pred xs
            | x :: xs -> x :: removeMany pred xs
            | _ -> []

    module Map =
        /// Returns a new map whose value stored under the key has been modified to `value`.
        /// This assumes that the key is contained in the map.
        let inline public update map key value =
            assert (Map.containsKey key map)

            Map.change
                key
                (function
                | _ -> Some value)
                map

        /// Returns a new map whose keys/values are the result of merging `map1` and `map2` according
        /// to a collision handling function `f`.
        let inline public join (map1: Map<'a, 'b>) (map2: Map<'a, 'b>) ([<InlineIfLambda>] f: 'a -> 'b -> 'b -> 'b) =

            let inline inner acc key value =
                match Map.tryFind key acc with
                | Some value' -> Map.add key (f key value value') acc
                | None -> Map.add key value acc

            Map.fold inner map1 map2

        let inline public mapKeyValue (mapping: 'a * 'b -> 'a * 'b) (map: Map<'a, 'b>) =
            Map.toArray map |> Array.map mapping |> Map.ofArray

        /// Adds a key/value pair to the Map and, if the key already exists, updates the associated value
        /// via the given updating function.
        let inline public addOrUpdate key value table updating =
            match Map.tryFind key table with
            | None -> Map.add key value table
            | Some oldValue -> update table key (updating oldValue)

        let inline public singleton key value = Map.ofList [ key, value ]

    let rec public digitCount number =
        if number < 10 then 1 else 1 + digitCount (number / 10)

    let public primeFactorDecompose (n: double) =

        let inline append c result =
            match Map.tryFind c result with
            | Some v -> Map.update result c (v + 1)
            | None -> Map.add c 1 result

        let rec inner (c: double) (p: double) (result: Map<double, int>) =
            if c < (pown p 2) then append c result
            elif c % p = 0. then inner (c / p) p (append p result)
            else inner c (p + 1.) result

        inner n 2. Map.empty

    let public cartProd lists =
        let inline inner xs ys =
            [ for x in xs do
                  for y in ys -> x :: y ]

        List.foldBack inner lists [ [] ]

//    let inline public isqrt (num: int) =
//        int (sqrt (float num))

    exception public IntegerSquareRootOfNegativeNumberException of int

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
