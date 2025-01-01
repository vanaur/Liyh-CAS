namespace Liyh.Kernel

//
// ‘True variable’ is just the name given to variables of the form SumPow `Name(string)`.
// This name is given because a variable can be an expression in its own right.
//

module public TrueVariable =
    open Liyh.Kernel
    open Liyh.Utils

    /// From the given expression, retrieve the "pure variables", i.e. the `Name(string)`.
    /// The function also proposes a list of names which may be part of the expression, but which are not
    /// variables (parameters, for example, or named constants).
    let public trueVariables (variable: SumPow) (excludedVariables: string list) =

        let rec inner result =
            function
            | Name a when not (List.contains a excludedVariables) -> a :: result
            | Fun(_, args) -> List.collect (inner result) args
            | SimplifiedSum.SimplifiedSum sum ->
                List.collect (fun a -> List.collect (fun (b, p) -> inner result b @ inner result p) a) sum
            | _ -> result

        inner [] variable |> List.distinct

    let public manyTrueVariables (variables: SumPow list) (excludedVariables: string list) =
        List.collect (fun v -> trueVariables v excludedVariables) variables |> List.distinct

    /// Checks whether the given expression contains at least a variable of the given variables.
    let public containsVariables (expr: SumPow) (variables: string list) =

        let rec inner =
            function
            | Name a -> List.contains a variables
            | Fun(_, args) -> List.containsBy inner args
            | SimplifiedSum.SimplifiedSum ss ->
                List.containsBy (fun lst -> List.containsBy (fun (b, p) -> inner b || inner p) lst) ss
            | _ -> false

        inner expr
