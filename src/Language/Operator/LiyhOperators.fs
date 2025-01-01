namespace Liyh.Language.Operator

module LiyhOperators =
    open System.Collections.Generic
    open FParsec

    type public OperatorName = string
    type public OpSide = string

    (* Operators with a numerically higher precedence value take precedence
       over operators with lower precedence values. *)

    let [<Literal>] public UnitPrecedence = 9
    let [<Literal>] public ExponentPrecedence = 4
    let [<Literal>] public MultiplicationPrecedence = 3
    let [<Literal>] public DivisionPrecedence = 3
    let [<Literal>] public ModuloPrecedence = 3
    let [<Literal>] public AdditionPrecedence = 2
    let [<Literal>] public SubstractionPrecedence = 2
    let [<Literal>] public EqualityPrecedence = 1

    type public 't LiyhOperator =
        | LiyhInfixOperator of OperatorName * 't InfixOperatorProperties
        | LiyhPostfixOperator of OperatorName * 't PostFixOperatorProperties
        | LiyhPrefixOperator of OperatorName * 't PrefixOperatorProperties
        | LiyhBasicOperator of 't BasicOperator

    and public 't BasicOperator =
        | OpEq of referTo: 't List // =
        | OpLe of referTo: 't List // <
        | OpLeq of referTo: 't List // <=
        | OpGr of referTo: 't List // >
        | OpGreq of referTo: 't List // >=
        | OpAdd of referTo: 't List // +
        | OpSub of referTo: 't List // -
        | OpMul of referTo: 't List // *
        | OpDiv of referTo: 't List // /
        | OpPow of referTo: 't List // ^
        | OpMod of referTo: 't List // mod
        | OpNeg of referTo: 't List // -

        override this.ToString() =
            match this with
            | OpEq _ -> "="
            | OpLe _ -> "<"
            | OpLeq _ -> "<="
            | OpGr _ -> ">"
            | OpGreq _ -> ">="
            | OpAdd _ -> "+"
            | OpSub _ -> "-"
            | OpMul _ -> "*"
            | OpDiv _ -> "/"
            | OpPow _ -> "^"
            | OpMod _ -> "mod"
            | OpNeg _ -> "-"

        member this.getPrior =
            match this with
            | OpEq _ -> EqualityPrecedence
            | OpLe _ -> EqualityPrecedence
            | OpLeq _ -> EqualityPrecedence
            | OpGr _ -> EqualityPrecedence
            | OpGreq _ -> EqualityPrecedence
            | OpAdd _ -> AdditionPrecedence
            | OpSub _ -> SubstractionPrecedence
            | OpMul _ -> MultiplicationPrecedence
            | OpDiv _ -> DivisionPrecedence
            | OpPow _ -> ExponentPrecedence
            | OpMod _ -> ModuloPrecedence
            | OpNeg _ -> UnitPrecedence

        member this.getReferTo =
            match this with
            | OpEq a -> a
            | OpLe a -> a
            | OpLeq a -> a
            | OpGr a -> a
            | OpGreq a -> a
            | OpAdd a -> a
            | OpSub a -> a
            | OpMul a -> a
            | OpDiv a -> a
            | OpPow a -> a
            | OpMod a -> a
            | OpNeg a -> a

    and public 't InfixOperatorProperties =
        { leftSide: OpSide
          rightSide: OpSide
          referTo: 't List
          assoc: Associativity
          prior: int }

    and public 't PostFixOperatorProperties =
        { leftSide: OpSide
          referTo: 't List
          assoc: bool
          prior: int }

    and public 't PrefixOperatorProperties =
        { rightSide: OpSide
          referTo: 't List
          assoc: bool
          prior: int }

    let private isDefaultOp =
        function
        | "+"
        | "-"
        | "*"
        | "/"
        | "^"
        | "mod"
        | ">"
        | ">="
        | "<"
        | "<="
        | "=" -> true
        | _ -> false

    /// Transforms a LEFT, RIGHT and NONE parsing associativity into a boolean.
    /// We have chosen that NONE reflects non-associativity.
    let public fpAssocToOptAssoc assoc = assoc <> Associativity.None

    /// This class lists the different operators that can be used in Liyh, those that are defined
    /// by default and natively as well as those added during parsing by the user.
    ///
    /// User-defined operators always refer to an expression which is, by definition, equivalent.
    /// Each operator therefore "refers" to the more fundamental expression. For example:
    /// ```txt
    /// notation x! is gamma[x + 1]
    /// with associativity: true
    ///      priority: 20
    /// ```
    /// Later, when processing expressions, whenever the postfix operator `_!` appears,
    /// it will be evaluatee exactly as `gamma[_+1]`.
    type public 't LiyhOperators(range: IEnumerable<'t LiyhOperator>) =
        let operatorList = new List<'t LiyhOperator>(range)

        do
            let basicOperatorList =
                [| OpEq(List<'t>())
                   OpLe(List<'t>())
                   OpLeq(List<'t>())
                   OpGr(List<'t>())
                   OpGreq(List<'t>())
                   OpAdd(List<'t>())
                   OpSub(List<'t>())
                   OpMul(List<'t>())
                   OpDiv(List<'t>())
                   OpPow(List<'t>())
                   OpMod(List<'t>())
                   OpNeg(List<'t>()) |]

                |> Array.map LiyhBasicOperator

            operatorList.AddRange basicOperatorList

        new() = LiyhOperators<'t>([])

        /// Returns the internal list.
        member __.getList = operatorList.AsReadOnly()

        /// Retrieves the operator given by its name. If not found, returns `None`.
        member __.tryFind opStr =

            let name =
                function
                | LiyhInfixOperator (name, _) -> name
                | LiyhPostfixOperator (name, _) -> name
                | LiyhPrefixOperator (name, _) -> name
                | LiyhBasicOperator op -> string op

            Seq.tryFind (fun op -> name op = opStr) operatorList

        (* Adding new operators *)

        member __.addLiyhInfixOp opStr prop =
            operatorList.Add(LiyhInfixOperator(opStr, prop))

        member __.addLiyhPostfixOp opStr prop =
            operatorList.Add(LiyhPostfixOperator(opStr, prop))

        member __.addLiyhPrefixOp opStr prop =
            operatorList.Add(LiyhPrefixOperator(opStr, prop))

        (* Adding new override operators *)

        member this.addLiyhInfixOpOverride opStr overrideReferTo =
            match this.tryFind opStr with
            | Some (LiyhInfixOperator (_, { referTo = referTo })) ->
                referTo.Add overrideReferTo
                true

            | Some (LiyhBasicOperator bop) ->
                bop.getReferTo.Add overrideReferTo
                true

            | _ -> false

        member this.addLiyhPostfixOpOverride opStr overrideReferTo =
            match this.tryFind opStr with
            | Some (LiyhPostfixOperator (_, { referTo = referTo })) ->
                referTo.Add overrideReferTo
                true

            | Some (LiyhBasicOperator bop) ->
                bop.getReferTo.Add overrideReferTo
                true

            | _ -> false

        member this.addLiyhPrefixOpOverride opStr overrideReferTo =
            match this.tryFind opStr with
            | Some (LiyhPrefixOperator (_, { referTo = referTo })) ->
                referTo.Add overrideReferTo
                true

            | Some (LiyhBasicOperator bop) ->
                bop.getReferTo.Add overrideReferTo
                true

            | _ -> false

        /// Retrieves the prioriy of the given operator by its name. If not found, returns `None`.
        member this.tryGetPrior opStr =
            let pred =
                function
                | LiyhInfixOperator (_, { prior = prior }) -> prior
                | LiyhPostfixOperator (_, { prior = prior }) -> prior
                | LiyhPrefixOperator (_, { prior = prior }) -> prior
                | LiyhBasicOperator op -> op.getPrior

            match this.tryFind opStr with
            | Some op -> Some(pred op)
            | None -> None

        /// Returns the equivalent of the given operator as defined in a program.
        member this.referTo(opStr: OperatorName) =
            match this.tryFind opStr with
            | Some op ->

                match op with
                | LiyhInfixOperator (_, prop) -> Some prop.referTo
                | LiyhPostfixOperator (_, prop) -> Some prop.referTo
                | LiyhPrefixOperator (_, prop) -> Some prop.referTo
                | _ -> None // The basic operators are managed by default.

            | None -> None

        /// Display the list of operators.
        member __.show() = printfn "%A" (Seq.toList operatorList)
