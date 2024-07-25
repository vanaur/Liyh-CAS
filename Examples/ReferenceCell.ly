namespace Ref (Ref, ::=)

   record Ref<t>
      mutable cell: t

   procedure Update[ref: Ref<t>, value: t]
      ref.cell <- value

   notation a ::= b is Update[a, b]
   with
      associativity: none
      priority: 8


use Ref

x := Ref[0]
do x ::= 7   # Now,  `x` is equal to 7.



