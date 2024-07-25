namespace Liyh.Kernel

[<AutoOpen>]
module rec Equation =
    open SumProd

    type public RelationKind =
        | Equality
        | Inequality of Inequality

    type public Inequality =
        | GreatherThan
        | LesserThan
        | GreatherEqualThan
        | LesserEqualThan

    type public AlgebraicEquation =
        { left: SumProd
          right: SumProd
          kind: RelationKind }
