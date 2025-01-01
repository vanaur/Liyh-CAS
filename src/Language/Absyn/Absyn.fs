namespace Liyh.Language.Absyn'

(* The abstract syntax tree of Liyh *)

module Absyn =
    open Liyh.Language.Syntax.Cosyn
    open Liyh.Language.Syntax.Location
    open Liyh.Kernel

    /// Instead of keeping the information in the AST directly, we associate each node
    /// in the tree with the relevant information.
    [<Struct>]
    type public NodeInfo<'t> =
        { location: Location
          ext: 't option }

        static member Default loc = { location = loc; ext = None }

    /// We assign a unique identifier to each node in the AST and place the auxiliary information in a map.
    type public AbsynMapInfo<'t> = Map<int, 't NodeInfo>

    let private updateNodeID = (+) 1

    let public cosynExprToSumPow ((cexpr, loc): CosynExpr) (nodeID: int) (mapInfo: AbsynMapInfo<_>) =
        let mapInfo = Map.add nodeID (NodeInfo.Default<_> loc)
        let nodeID = updateNodeID nodeID

        0

    // let private opNameToSymbolic ((str, loc): OpName)

    //    let public cosynExprToSymbolic ((expr, loc): CosynExpr) (nodeID: int) (mapInfo: AbsynMapInfo<_>) =
    //        let mapInfo = Map.add nodeID (NodeInfo.Default<_> loc)
    //        let nodeID = updateNodeID nodeID
    //
    //        match expr with
    //        | CosynExpr'.ExprBinOpCall((opName, _), lhs, rhs) -> ...

    let private qualName (qual: OpName list) (name: OpName) =
        let rec inner result = function
            | [] -> result
            | [ (name, _) ] -> name
            | (name, _) :: xs -> inner (sprintf "%s.%s" result name) xs
        inner "" (qual @ [name])

    let rec public cosynExprToSymbolic = function
        | CosynExpr'.ExprBinOpCall((name, _), lhs, rhs), _ ->
            { atom = Atom.Identifier name
              attributes = [ ("lhs", cosynExprToSymbolic lhs); ("rhs", cosynExprToSymbolic rhs) ] }

        | CosynExpr'.ExprName (qual, name), _ ->
            { atom = Atom.Identifier(qualName qual name)
              attributes = [] }

        | CosynExpr'.ExprLiteral(CosynLit.Integer x), _ ->
            { atom = Atom.Const(Constant x)
              attributes = [] }

        | CosynExpr'.ExprLiteral(CosynLit.Float x), _ ->
            { atom = Atom.Const(Constant x)
              attributes = [] }

        | CosynExpr'.ExprNegation x, _ ->
            { atom = Atom.Identifier "Neg"
              attributes = [ null, cosynExprToSymbolic x ] }

        | CosynExpr'.ExprPrefixOpCall((name, _), x), _ ->
            { atom = Atom.Identifier name
              attributes = [ null, cosynExprToSymbolic x ] }

        | CosynExpr'.ExprParens x, _ -> cosynExprToSymbolic x

        | CosynExpr'.ExprProcCall ({ name = (qual, name); arguments = arguments }, _), _ ->
            let name = qualName qual name
            let args = List.map (fun { name = name; value = value } -> null, cosynExprToSymbolic value) arguments
            
            { atom = Atom.Identifier name
              attributes = args }

        | CosynExpr'.ExprWithUnicodeExponent(cexpr, exp), _ ->
            { atom = Atom.Identifier "**"
              attributes = [(null, cosynExprToSymbolic cexpr); (null, { atom = Atom.Const(Constant exp); attributes = [] })] }

        | CosynExpr'.ExprTensorIndexNotation(tin, _), _ ->
            let inline inner index =
                match index with
                | TDown (x, _) -> "index", { atom = Atom.Identifier "CovariantIndex"; attributes = [ "indexName", { atom = Atom.Identifier x; attributes = [] } ] }
                | TUp (x, _) -> "index", { atom = Atom.Identifier "ContravariantIndex"; attributes = [ "indexName", { atom = Atom.Identifier x; attributes = [] } ] }
            
            let tname = { atom = Atom.Identifier (fst tin.tname); attributes = [] }
            let indices = { atom = Atom.Identifier "Indices"; attributes = List.map inner tin.indices }

            { atom = Atom.Identifier "IndexedTensor"
              attributes = [ ("name", tname); ("indices", indices) ] }

        | s -> failwithf "TODO: %A" s

// On ne peut faire ça qu'après le typage...
// Typiquement, est-ce que F[x] + 1 est une expression symbolique ou un truc normal ? ...
