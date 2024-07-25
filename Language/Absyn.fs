namespace Liyh.Language

module Absyn =
    open System
    open Liyh.Kernel.SumProd
    open Liyh.Language.Syntax.Location
    open Liyh.Language.Scope
    open Liyh.Language.Syntax.Cosyn

    let inline private ctspNegation f x = Prod [ SumProd.Integer -1I; f x ]

    let rec private binOpToSumOrProd op =

        let rec inner = function
            | ExprParens (a, _), ExprParens (b, _)
            | ExprParens (a, _), b
            | a, ExprParens (b, _) -> inner (a, b)
            | ExprBinOpCall ((iop, _), (a, _), (b, _)), r when iop = op -> hparens a b r
            | l, ExprBinOpCall ((iop, _), (c, _), (d, _)) when iop = op -> hparens c d l
            | x, y -> [ x; y ]

        and hparens x y = function
            | ExprBinOpCall ((iop, _), (x', _), (y', _))
            | ExprParens (ExprBinOpCall ((iop, _), (x', _), (y', _)), _) when iop = op -> inner (x, y) @ inner (x', y')
            | ExprParens ((z, _))
            | z -> inner (x, y) @ [ z ]

        inner

    exception public UnknownBinaryOperatorException of string

    /// Converts the concrete representation entered by the user into the abstract representation of the core
    /// algebra engine, allowing access to the evaluation of expressions. Meta-information is no longer retained.
    let rec public cosynToSumProd = function
        | ExprName (_, (name, _)) -> Variable name
        | ExprLiteral (Integer x) -> SumProd.Integer(bigint x)
        | ExprLiteral (Float x) -> SumProd.Float(x)
        | ExprNegation ((ExprLiteral (Integer x), _)) -> SumProd.Integer -(bigint x)
        | ExprNegation ((x, _)) -> ctspNegation cosynToSumProd x
        | ExprBinOpCall ((op, _), (a, _), (b, _)) ->
            match op with
            | "**" -> Pow(cosynToSumProd a, cosynToSumProd b)
            | "/" -> frac (cosynToSumProd a, cosynToSumProd b)
            | op ->
                let temp =
                    binOpToSumOrProd op (a, b)
                    |> List.map cosynToSumProd

                match op with
                | "+" -> Sum temp
                | "*" -> Prod temp
                | "-" ->
                    temp.Head :: List.map (ctspNegation id) temp.Tail
                    |> Sum
                | _ -> raise (UnknownBinaryOperatorException op)

        | ExprPrefixOpCall (("-", _), (ExprLiteral (Integer x), _)) -> SumProd.Integer -(bigint x)
        | ExprPrefixOpCall (("-", _), (a, _)) -> ctspNegation cosynToSumProd a

        | ExprProcCall ({ name = (_, (name, _))
                          arguments = arguments },
                        _) ->
            Function(name, List.map (fun ({ value = (value, _) }: CosynArg) -> cosynToSumProd value) arguments)

        | ExprParens ((x, _)) -> cosynToSumProd x
        | ExprInfinity -> Infinity
        | ExprWithUnicodeExponent ((base', _), exp) -> Pow(cosynToSumProd base', SumProd.Integer (bigint exp))
        | s ->
            printfn "TODO: %A" s
            Null

    /// Abstract syntax tree of Liyh's underlying intermediate language for top level statements and expressions.
    type public AbsynTopL =
        | AbsynTopLPerform of SumProd
        | AbsnyTopLDo of SumProd
        | AbsynTopLDefineVariable of string * SumProd
        | AbsynTopLDefineProcedure of string * AbsynTopL list

    let public cosynToAbsyn = function
        | TopLPerform (expr, _) -> AbsynTopLPerform (cosynToSumProd expr)
        | TopLDo (expr, _) -> AbsnyTopLDo (cosynToSumProd expr)
    //  | TopLConstDef ({name = name; value = value}, _) -> AbsynTopLDefineVariable (name, value)
        | _ -> raise (Exception "Not implemented yet.")

module AbstractSyntaxTree =
    open Liyh.Kernel.SumPow
    open Liyh.Language.Syntax.Cosyn

    type public AbsynTopLevel = int
    