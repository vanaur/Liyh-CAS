namespace Liyh.Kernel

// Implements naive and basic elements of set theory that are useful in Liyh's computations.

[<RequireQualifiedAccess>]
module rec SymbolicSet =
    open System
    open Liyh.Kernel.Atomic

    type private ISymbolicConstraint<'T when 'T :> ISymbolic> = 'T
    type public ISymbolicComparaison = ISymbolic -> ISymbolic -> int

    [<Symbolic>]
    type public SymbolicSet<'T when 'T :> ISymbolic> =
        | Empty                     // { }
        | Singleton of 'T           // { s }
        | Enumerated of 'T list     // { s₁; s₂; ...; sₙ }
        | Predicated of 'T * 'T     // { F(s) | P(s) }

        interface ISymbolic with
            member this.ToSymbolic() = toSymbolic this
            member this.ToLatex() = Some (toLatex this)
            member this.ToLatexOrString() = toLatex this
            member this.Hash = 0

    let rec private toSymbolic =
        function
        | Empty ->
            atom (Identifier "EmptySet")
       
        | Singleton x ->
            { atom = Identifier "SingletonSet"
              attributes = [ null, Atomic.toSymbolic x ] }

        | Enumerated xs ->
            { atom = Identifier "EnumeratedSet"
              attributes = List.map (fun x -> null, Atomic.toSymbolic x) xs }

        | Predicated (f, p) ->
            { atom = Identifier "PredicatedSet"
              attributes = [ ("expression", Atomic.toSymbolic f)
                             ("predicate", Atomic.toSymbolic p) ] }

    let private toLatex =
        function
        | Enumerated []
        | Empty -> sprintf @"\empty"
        | Singleton x -> sprintf @"\left\{ %s \right\}" (toLatexOrString x)
        | Enumerated xs -> sprintf @"\left\{ %s \right\}" (System.String.Join(";", List.map toLatexOrString xs))
        | Predicated (f, p) -> sprintf @"\left\{ \left. %s \right| %s \right\}" (toLatexOrString f) (toLatexOrString p)

    let private hashSymbolicSet =
        function
        | Enumerated []
        | Empty -> hash Empty
        | Enumerated [ x ]
        | Singleton x -> HashCode.Combine(Singleton, x)
        | Enumerated xs -> HashCode.Combine(Enumerated, xs)
        | Predicated (f, p) -> HashCode.Combine(Predicated, f, p)

