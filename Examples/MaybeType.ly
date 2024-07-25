namespace Maybe(Maybe, IsJust, IsNothing, GetJustOrDefault)

   enumeration Maybe<t>
      Just[value: t]
      Nothing

   procedure
      IsJust[Just[_]] -> True
      IsJust[Nothing] -> False
    
   procedure
      IsNothing[Just[_]] -> False
      IsNothing[Nothing] -> True

   procedure
      GetJustOrDefault[Just[x], default] -> x
      GetJustOrDefault[Nothing, default] -> default


use Maybe

myValue := Just['Hello, world!']

do select myValue
      Nothing -> Write['This is nothing']
      Just[x] -> Write['This is {x}']

