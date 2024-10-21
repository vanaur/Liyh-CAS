namespace Liyh.Kernel

/// This module contains utilities concerning index notations, mainly to be used in Ricci's
/// calculus (with Einstein's summation notations), but could be used without tensor in mind.
module public rec Index =
    open Liyh.Utils

    exception public NoMoreUsableNameForIndicesException
    exception public UnknownIndexNameException of string
    exception public InconsistentContextException of IndexContext
    exception public CannotRenameFreeIndexException of string

    let private lowercaseLatinLetters =
        [| "a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"
           "m"; "n"; "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w"; "x"
           "y"; "z" |]

    let private lowercaseGreekLetters = 
        [| "α"; "β"; "γ"; "δ"; "ϵ"; "ζ"; "η"; "θ"; "ι"; "κ"; "λ"; "μ" 
           "ν"; "ξ"; "ο"; "π"; "ρ"; "σ"; "τ"; "υ"; "ϕ"; "χ"; "ψ"; "ω"
           "ϐ"; "ε"; "ϰ"; "ϑ"; "ϖ"; "ϱ"; "ς" |]

    let private greekLettersName =
        [| "alpha"; "beta"; "gamma"; "delta"; "epsilon"; "zeta"; "eta"; "theta"; 
           "iota"; "kappa"; "lambda"; "mu"; "nu"; "xi"; "omicron"; "pi"; 
           "rho"; "sigma"; "tau"; "upsilon"; "phi"; "chi"; "psi"; "omega"
           "varbeta"; "varepsilon"; "varkappa"; "vartheta"; "varpi"; "varrho"; "varsigma" |]

    /// Determines whether the index name is Latin or Greek.
    let public getBuiltinNotationFromName (name: string) =
        let name = name.ToLower()

        if Array.contains name greekLettersName || Array.contains name lowercaseGreekLetters
        then IndexLetterNotation.Greek
        else IndexLetterNotation.Latin

    /// Specifies how a vector is decomposed. In practice, it just means where the index is placed.
    /// See https://en.wikipedia.org/wiki/Covariance_and_contravariance_of_vectors.
    [<Struct>]
    type public Variance =
        | Covariant     // Notation of lower index.
        | Contravariant // Notation of upper index.

    /// Specifies the free indices and bound indices.
    /// See https://en.wikipedia.org/wiki/Free_variables_and_bound_variables.
    [<Struct>]
    type public IndexUsage =
        | FreeIndex     // The index is not a summation index and therefore cannot be changed.
        | DummyIndex    // The index is used in summation and is therefore arbitrarily denominated.

    /// Specifies the notational convention to be used for an index, generally in physics Latin indices are
    /// for spacial components while greeks are used for spacio-temporal components.
    [<Struct; RequireQualifiedAccess; NoComparison; NoEquality>]
    type public IndexLetterNotation =
        | Greek
        | Latin
        | Other of string array

    let private getConventionalNames =
        function
        | IndexLetterNotation.Greek -> lowercaseGreekLetters
        | IndexLetterNotation.Latin -> lowercaseLatinLetters
        | IndexLetterNotation.Other other -> other

    /// Specifies the information carried by an index.
    type public Index =
        { attachedTo: string               // Indicates which symbol the index is attached to
          possibleValues: int list option  // Describes the possible natural numbers that the index can take
          variance: Variance               // Indicates whether index is up or down
          usage: IndexUsage                // Indicates whether the index is used or free
          notation: IndexLetterNotation    // Specifies how to write the index name
          name: string }                   // The index name

    let public toLatexIndex { variance = variance; name = name } =
        let name =
            match Array.tryFindIndex (( = ) (name.ToLower())) greekLettersName with
            | Some i -> lowercaseGreekLetters.[i]
            | None -> if name.Length > 1 then sprintf @"\text{%s}" name else name

        sprintf @"{}%s{%s}" (if variance = Covariant then "_" else "^") name

    /// For a given "indexed expression", this is the context of used indices.
    type public IndexContext =
        { context: Index list }

    /// Checks if the given context use the given index's name.
    let inline private isUsed (name: string) { context = ctx } =
        List.containsBy (fun index -> index.name = name) ctx

    /// Determines whether the given index is free or summed.
    let inline private isFreeIndex { usage = usage } =
        usage = FreeIndex

    /// Generates a new, unused index name. If no more indexes are available, throw an exception.
    let public newIndexName (notation: IndexLetterNotation) (context: IndexContext) =
        getConventionalNames notation
        |> Array.tryFind (not << flip isUsed context)
        // It's a kind of a lazy solution to throw an exception,
        // we could for example take up the first index's name and add a `'` or a number and so on.
        |> Option.defaultWith (fun _ -> raise NoMoreUsableNameForIndicesException)

    /// Defines a new index given the given properties, and updates the context accordingly.
    /// The index has a name automatically generated from the given context.
    let inline public newIndex
        (attachedTo: string)
        (possibleValues: int list option)
        (variance: Variance)
        (usage: IndexUsage)
        (notation: IndexLetterNotation)
        (context: IndexContext) =

        let index =
            { attachedTo = attachedTo
              possibleValues = possibleValues
              variance = variance
              usage = usage
              notation = notation
              name = newIndexName notation context }

        index, { context with context = index :: context.context }

    /// Updates the context by renaming a dummy index. If the index is a free index, then raise an exception.
    let public rename (oldName: string) (newName: string) (context: IndexContext) =
        match List.tryFindIndex (fun index -> index.name = oldName) context.context with
        | None -> raise (UnknownIndexNameException oldName)
        | Some i ->
            let old = context.context.[i]

            if isFreeIndex old then
                raise (CannotRenameFreeIndexException old.name)

            let ctx = List.removeAt i context.context

            { context = { old with name = newName } :: ctx }

    /// Updates the context by deleting the specified index, if present.
    let public remove (name: string) (context: IndexContext) =
        match List.tryFindIndex (fun index -> index.name = name) context.context with
        | None -> context
        | Some i -> { context = List.removeAt i context.context }

    /// Merges the two given index contexts. If there are overlapping index names, then automatically
    /// renames them and returns a Map of oldName -> newName.
    let public merge { context = context1 } { context = context2 } =
        let names1 = List.map (fun index -> index.name) context1
        let names2 = List.map (fun index -> index.name) context2

        // If the indexes don't mix, if they're all differently named, then there's nothing more to be done.
        if List.length names1 = List.length names2 && not (List.areEquivalent names1 names2) then
            printfn "%A" (names1, names2)
            { context = context1 @ context2 }, Map.empty

        // If indexes in the second context have the same names as those in the first context, then we rename
        // them and return a Map describing which index of the second context is renamed by what.
        else
            let rec inner map ctx =
                function
                | [] -> ctx, map
                | index :: rest when isUsed index.name ctx ->
                    let newName = newIndexName index.notation ctx
                    let newCtx = { ctx with context = { index with name = newName } :: ctx.context }

                    inner (Map.add index.name newName map) newCtx rest

                | index :: rest ->
                    inner map { ctx with context = index :: ctx.context } rest

            inner Map.empty { context = context1 } context2

    /// Merges a list of index contexts. If there are overlapping index names, then automatically
    /// renames them and returns a Map of oldName -> newName.
    let public mergeMany (contexts: IndexContext list) =
        match contexts with
        | [] -> invalidArg "contexts" "The given list of context must be non-empty."
        | ctx :: [] -> ctx, Map.empty
        | ctx1 :: ctx2 :: [] -> merge ctx1 ctx2
        | ctx1 :: ctx2 :: ctxs ->
            List.fold
                (fun (ctx1, map) ctx2 ->
                    let ctx', map' = merge ctx1 ctx2
                    // The exception might not happen
                    ctx', Map.join map map' (fun _ -> failwith "Key conflicts in a context merge "))
                (merge ctx1 ctx2) ctxs

    /// Check that the dummy indices are summed consistently according to Einstein's notation.
    let public isIndexConsistent { context = ctx } =

        let check =
            snd >> function
            | xs when List.length xs <> 2 -> false                  // Summation is done by pairs and
            | [ { variance = v1 }; { variance = v2 } ] -> v1 <> v2  // between a covariant and a contravariant index.
            | _ -> false

        List.filter (fun index -> index.usage = DummyIndex) ctx
        |> List.groupBy _.name
        |> List.forall check

    /// If the context is consistent, then returns the list of contracted indices, otherwise throws an exception.
    let public getContractedIndices (context: IndexContext) =
        if not (isIndexConsistent context) then raise (InconsistentContextException context) else

        context.context
        |> List.filter (fun index -> index.usage = DummyIndex)
        |> List.map _.name
        |> List.distinct

