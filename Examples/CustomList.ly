
enumeration List with t
   Cons[head: t, tail: List<t>]
   Nil

notation x ++ xs is Cons[x, xs]
with
   associativity: Left
   priority: priorityOf[+]

||| Length: List<t> -> Natural
procedure
   Length[Cons[head: _, tail: ys]] -> Length[ys] + 1
   Length[Nil] -> 0

||| StringToList: String -> List<Unicode>
procedure StringToList[str: String]
   mutable result := Nil
   for c in str
      result <- Cons[c, result]
   return result

||| example: String
example := "Hello, world!"

||| converted: List<Unicode>
converted := example :: region List<Unicode>

||| ListToString: List<Unicode> -> String
procedure
   ListToString[Cons[head: x, tail: ys]] -> x + ListToString[ys]
   ListToString[Nil] -> ""

notation lst :: T is ListToString[lst]

||| other: String
other := converted :: region String

||| size: Natural
size := Length[other]

||| Find: t -> List<t> -> ?Natural -> Maybe<Natural>
procedure
   Find[_, Nil] -> Nothing[]
   Find[x, Cons[head: y, tail: ys], n] when x = y -> Just[n]
   Find[x, Cons[head: _, tail: ys], n] -> Find[x, ys, n + 1]
   Find[x, xs] -> Find[x, xs, 0]

||| xs: List<Natural>
xs := 0 ++ 1 ++ 2 ++ Nil   # xs = Cons[0, Cons[1, Cons[2, Nil]]]

perform Write[xs]
