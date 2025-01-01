namespace Liyh.Kernel

module Prime =
    open System.Collections
    open Liyh.Utils

    /// Generates the `nmax` first prime numbers.
    let public generatePrimes (nmax: int) =
        let sieve = new BitArray((nmax / 2) + 1, true)
        let result = new ResizeArray<int>(nmax / 10)

        if nmax > 1 then
            result.Add 2

        let mutable m = 1

        while 2 * m + 1 <= nmax do
            if sieve.[m] then
                let n = 2 * m + 1

                if n <= isqrt nmax then
                    let mutable i = m

                    while 2 * i < nmax do
                        sieve.[i] <- false
                        i <- i + n

                result.Add n

            m <- m + 1

        Array.ofSeq result

    /// Check if the given number is prime.
    let public isPrime (n: int) =

        let rec loop d i =
            if d > isqrt n then true
            else if n % d = 0 then false
                 else loop (d + i) (6 - i)

        loop n 2

    /// Returns the prime factorization of the given number.
    let public primeFactors (n: int) =
        let result = new ResizeArray<int>(int (log (double n) / log 2.))
        let mutable current = n

        while current % 2 = 0 do
            result.Add 2
            current <- current / 2
        
        for i in 3 .. 2 .. isqrt n + 1 do
            while current % i = 0 do
                result.Add i
                current <- current / i
        
        if current > 2 then
            result.Add current
        
        Array.ofSeq result

    /// Returns the prime factorization of the given number with associated exponent.
    let public uniquePrimeFactors (n: int) =
        dict (Seq.countBy id (primeFactors n))

