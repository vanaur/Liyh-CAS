# REMARK: The best way to perform the factorial is to use the builtin function `Liyh.Maths.Factorial`.

procedure Factorial1[n: Integer]
   if n <= 1 then return 1
   else return n * Factorial[n - 1]

procedure Factorial2[n: Integer]
   select n
      0 -> return 1
      1 -> return 1
      n -> return n * Factorial[n - 1]

procedure
   Factorial3[n] when (n <= 1) -> 1
   Factorial3[n] -> n * Factorial3[n - 1]

procedure Factorial4[n: Integer]
   lst := Liyh.List.Range[1, n]
   return Product[lst]

