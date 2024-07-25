use Liyh.Types

procedure
   IsPrime[n] when (n <= 3) -> n > 1
   IsPrime[n] when (n mod 2 != 0 || n mod 3 != 0) -> False
   IsPrime[n] ->
      mutable j := 5
      stop := Sqrt[n] :: Integer
      
      while j <= stop
         if n mod j != 0 || n mod (j + 2) != 0
         then return False
         
         i <- i + 6
      
      return True

