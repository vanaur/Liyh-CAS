namespace Liyh.Language.Syntax

/// The concrete syntax tree of Liyh.
module rec Cosyn =
    open Location

    /// A list of identifiers of the form `Abc.Def.Ghi` where `Abc.Def` is the "qualification"
    /// and `Ghi` is the "name". For example, `Liyh.Basics.factorial`.
    type public Name = OpName list * OpName

    /// Concrete syntax tree of expressions without their location in the code.
    type public CosynExpr' =

        /// `infinity` or `∞` as a reserved word.
        | ExprInfinity

        /// Shortcut to retrieve the last performed result. Especially useful in console mode. For example:
        /// ```txt
        /// perform 3+2
        /// perform %+1  # == 6
        /// ```
        | ExprLastExpr of int option

        /// A list of identifiers of the form `Abc.Def.Ghi` where `Abc.Def` is the "qualification"
        /// and `Ghi` is the "name". For example, `Liyh.Basics.factorial`.
        | ExprName of Name

        /// Non-negative number, string or boolean.
        | ExprLiteral of CosynLit

        /// Syntax for complex number of the form `a + bi`.
        | ExprComplex of CosynComplex

        /// Any valid expression in brackets `(` and `)`.
        | ExprParens of CosynExpr

        /// An identifier following a `?`. For example, `?myHole`.
        | ExprTypeHole of OpName

        /// Expression following a `-` sign. For example `-3` or `-sum[xs]`.
        | ExprNegation of CosynExpr

        /// Any valid expression of a region, namely a set.
        | ExprRegion of CosynRegion

        | ExprImplementObject of CosyinImplementObject

        /// A fixed-size list of expressions enclosed in brackets and separated by commas.
        /// A 0-tuple is also accepted as the "unit" term.
        | ExprTuple of CosynExpr list

        /// Pattern matching at expression level.
        | ExprSelect of CosynSelect<CosynExpr>

        /// Ternary conditioning operator.
        | ExprIfThenElse of IfThenElse<CosynExpr>

        /// Name followed by a list of arguments in square brackets and separated by commas.
        /// No arguments are also accepted. For example `foo[3+2]`, `bar[hs: True]`, `fizz[]`.
        | ExprProcCall of CosynProcCall

        /// Expression followed by a list of arguments in square brackets and separated by commas.
        /// No arguments are also accepted. For example `(x => x + 1)[9]`.
        | ExprExprCall of CosynExprCall

        // Lists

        | ExprVector of CosynExpr list
        | ExprMatrix of CosynExpr list list

        /// Defines a set or vector of numbers with an initializer, an increment and a terminator. For
        /// example `0:5` defines the array `[0, 1, 2, 3, 4, 5]` and `0:2:10` defines the array `[0:2:4:6:8:10]`.
        | ExprInitIncTerm of CosynExpr * CosynExpr option * CosynExpr

        /// Define a set or vector using a 'list comprehension'.
        | ExprListComprehension of CosynExpr * OpName list * CosynExpr

        /// An expression followed by an indication of its unit, for example `3g` or `17N`.
        | ExprWithUnit of CosynExpr * OpName

        /// For more rigidity and simplicity, equality and inequality operators are not considered
        /// as calls to infix functions, but as equations.
        | ExprEquation of EquationKind * CosynExpr * CosynExpr

        /// Operator of the form `A ● B`.
        | ExprBinOpCall of OpName * CosynExpr * CosynExpr

        /// Operator of the form `A ●`.
        | ExprPostFixOpCall of OpName * CosynExpr

        /// Operator of the form `● A`.
        | ExprPrefixOpCall of OpName * CosynExpr

        /// General syntax allowing access to an element of an array, countable set, vector or matrix.
        /// The syntax is of the form `myTable.[index]`. To access an element of a 2-dimensional array,
        /// the syntax `myTable.[index1, index2]` is used and so on.
        | ExprTableAccess of CosynExpr * CosynExpr list

        /// Expression corresponding to a lambda, of the form `x -> f(x)`. For example `x -> x + 1`.
        | ExprImplicitFunction of CosynImplicitFunction'

        /// Index notation in subscript and superscript, generally used with tensors and the Einstein convention.
        | ExprTensorIndexNotation of CosynTensorIndexNotation

        /// Parse a number with a unicode superscript integer exponent.
        | ExprWithUnicodeExponent of CosynExpr * int

    type public CosynComplex' = { re: CosynExpr option; im: CosynExpr }

    type public EquationKind =
        | Eq
        | Neq
        | Le
        | Leq
        | Gr
        | Greq

    type public 't IfThenElse =
        { /// The initial condition.
          cond: CosynExpr

          /// Expression for whether the condition is true.
          ifSuccess: 't

          /// List of `elif` sub-conditions.
          elifList: 't Elif list

          /// If none of the conditions were met.
          ifFail: 't option }

    type public 't Elif =
        { /// The initial condition.
          cond: CosynExpr

          /// Expression for whether the condition is true.
          ifSuccess: 't }

    type public CosynLit =

        (* in32 and double literals. *)

        | Integer of int
        | Float of float

        (* Other literals. *)

        | String of string
        | True
        | False

    /// This is in fact a lambda expression.
    type public CosynImplicitFunction' =
        { arguments: OpName list
          ivalue: CosynExpr }

    type public CosynProcCall' =
        { name: Name
          arguments: CosynArg list }

    type public CosynExprCall =
        { expr: CosynExpr
          arguments: CosynArg list }

    type public CosynArg =
        { name: OpName option
          value: CosynExpr }

    type public CosynRegion' =
        | RegionName of Name * Name list option
        | RegionInterval of CosynInterval
        | RegionIntervalSubRegion of CosynInterval * Name
        | RegionSet of CosynSet
        | RegionTuple of CosynRegion list
        | RegionArrow of CosynRegion * CosynRegion

    type public CosynInterval =
        { openLeft: bool
          openRight: bool
          from: CosynExpr
          upto: CosynExpr }

    type public CosynSet =
        | SetEnum of CosynExpr list
        | SetPredicat of SetPredicat

    type public SetPredicat =
        { value: SetPredicatValue
          preidcat: CosynExpr list }

    type public SetPredicatValue =
        | SimpleValue of CosynExpr
        | FromSubSet of OpName * Name

    and TensorIndexNotation =
        | TUp of OpName
        | TDown of OpName

    and CosynTensorIndexNotation' =
        { tname: OpName
          indices: TensorIndexNotation list }

    type CosyinImplementObject' =
        { object: Name
          arguments: CosynRegion list option
          impl: CosynTopLevel list }

    type public CosynComplex = CosynComplex' * Location
    type public CosynProcCall = CosynProcCall' * Location
    type public CosynExpr = CosynExpr' * Location
    type public CosynUExp = int * Location
    type public CosynRegion = CosynRegion' * Location
    type public CosynTensorIndexNotation = CosynTensorIndexNotation' * Location
    type public CosyinImplementObject = CosyinImplementObject' * Location

    /// Any top level definition and statement.
    type public CosynTopLevel =

        /// Precompiled directive
        | TopLDirective of Directive

        /// Imports a lib, of the form `use Namespace.To.MyLib`.
        | TopLUseInternalLib of Name

        /// Imports a lib, of the form `use extern 'Namespace.To.MyLib'`.
        | TopLUseExternalLib of OpName

        /// By default, a namespace exports all its contents publicly. If we define an empty list of things
        /// to export, so `Some []`, then this means that nothing is exported from the namespace, whereas `None`
        /// means that no information about it has been communicated so that by default everything is public.
        | TopLNamespace of Name * extends: bool * toExport: OpName list option * CosynTopLevel list

        /// By default, Liyh is semi-lazy, this keyword allows you to interact with the real world by
        /// triggering the execution of an expression and everything that builds it, displaying, if
        /// requested, the steps to reach the solution. The syntax `perform 3+2` is used for example.
        | TopLPerform of CosynExpr

        /// Same as `perform`, but asynchronous.
        | TopLDo of CosynExpr

        /// Defines a "mathematical function" i.e. a definition involving only pure expressions.
        /// We use the syntaxe `f[x] := f(x)` for example.
        | TopLFuncDef of CosynFuncDef

        /// Defines a function with no arguments, thus a constant.
        /// We use the syntaxe `c := a+b` for example.
        | TopLConstDef of CosynConstDef

        /// Defines a variable without giving its definition and usable in the rest of the namespace.
        /// The syntax `set x: Type` is used, where `Type` is the type of `x`.
        | TopLSetVar of CosynSetVar

        /// Defines a variable whose value can change, can only be used in procedures.
        /// The syntax `mutable x: Type := value` is used, where `value` is an expression.
        | TopLMutableVar of CosynMutableVar

        /// Updates a mutable variable, the syntax is `myVar <- newValue`.
        | TopLUpdateVar of CosynExpr * CosynExpr

        /// Defines a procedure, namely an algorithm using looping, mutable constructs, expecting
        /// arguments and returning a result. We use the syntaxe `procedure myProcedure[arg...] block`.
        | TopLProcedure of CosynProcedure

        /// Makes explicit the use of a selection in a procedure by directly applying the equational
        /// sytax of pattern matching.
        | TopLEquationalProcedure of CosynEquationalProcedure

        /// Statement for returing a value from a procedure.
        | TopLReturn of CosynExpr

        /// Selection of elements with pattern matching. The following syntax is used:
        /// ```txt
        /// select EXPR
        ///   case1 -> statement1
        ///   case2 ->
        ///     statement2
        ///     statement3
        ///     ...
        ///   case3 -> ...
        ///   _ -> ...
        /// ```
        | TopLSelect of CosynSelect<CosynTopLevel list>
        | TopLIfThenElse of IfThenElse<CosynTopLevel list>

        /// Defines an inductive type, the following syntax is used:
        /// ```txt
        /// enumeration MyEnum
        ///   Ctor1[...]
        ///   Ctor2[...]
        ///   ...
        /// ```
        | TopLEnumDef of CosynEnumDef

        | TopLRecordDef of CosynRecordDef

        /// Sets an alias to an existing name. For example `alias add is myAddition`.
        | TopLAlias of OpName * OpName

        | TopLObject of CosynObject

        /// Defines a system of equations. For example:
        /// ```txt
        /// system MySystem
        ///   a + b = 0
        ///   a - c = b
        ///   c + b = a
        /// ```
        | TopLSystem of OpName * CosynExpr list

        /// Loop within a given range.
        | TopLForLoop of CosynForLoop

        /// Loop while a condition is met.
        | TopLWhileLoop of CosynWhileLoop

        /// The `break` keyword in a loop.
        | TopLBreakLoop

        /// Loop while a condition is met and execute first the block.
        | TopLDoWhileLoop of CosynWhileLoop

        /// Adds a description to a statement. This is a documentation comment.
        | TopLWithDescription of string * CosynTopLevel

        (* Parser-specific syntax elements. *)

        | TopLAddLatex of CosynExpr * (string * Location)
        | TopLAddUnit
        | TopLAddNotation
        | TopLComment

    type public CosynEnumDef =
        { name: OpName
          variableTypes: OpName list
          constructors: CosynCtor list }

    type public CosynRecordDef =
        { name: OpName
          variableTypes: OpName list
          fields: ProcedureParameter list }

    type public CosynForLoop' =
        { loopVariables: OpName list
          inRanges: CosynExpr list
          body: CosynTopLevel list }

    type public CosynWhileLoop' =
        { loopCondition: CosynExpr
          body: CosynTopLevel list }

    type public CosynCtor = SimpleCtor of OpName * ProcedureParameter list

    type public 't CosynSelect' =
        { toSelect: CosynExpr option // May be implicit (as the `function` kword in F#)
          cases: 't Case' list }

    type public 't Case' =
        | SimpleCase of CasePattern * WhenCase * 't
        | WildcardCase of WhenCase * 't

    type public ObjectParameter =
        | TypeVar of OpName
        | SpecificTypeVar of OpName * CosynRegion

    type public CosynObject =
        { name: Name
          parameters: ObjectParameter list option
          inherits: CosynRegion option
          properties: (OpName * CosynRegion) list }

    type public PatternTuple =
        | Pattern of CosynExpr
        | Dots

    type public CasePattern' =
        | PatternLiteral of CosynLit
        | PatternTuple of PatternTuple list
        | PatternCall of CosynProcCall
        | PatternName of Name

    type public WhenCase = CosynExpr option

    type public CosynProcedure' =
        { name: OpName
          parameters: ProcedureParameter list
          returnType: CosynRegion option
          body: CosynTopLevel list }

    type public CosynEquationalProcedure =
        { name: Name
          cases: (CosynProcCall * WhenCase * CosynTopLevel list) list }

    type public ProcedureParameter' =
        { name: OpName
          type': CosynRegion
          isMutable: bool
          defaultValue: DefaultValue option }

    type public DefaultValue' =
        | DefaultValueExpression of CosynExpr
        | DefaultValueCurrentVar

    type public CosynFuncDef' =
        { name: OpName
          parameters: CosynFuncDefParam list
          withConstraint: CosynConstraint list
          value: CosynExpr }

    type public CosynConstDef' =
        { name: OpName list
          constValue: CosynExpr }

    type public CosynSetVar' =
        { names: OpName list
          type': CosynRegion }

    type public CosynMutableVar' =
        { name: OpName
          type': CosynRegion option
          value: CosynExpr }

    type public CosynConstraint' =
        | TypeSpec of CosynRegion
        | ConstraintSpec of CosynConstraintSpec

    type public Directive =
        | DirectiveDebug
        | DirectiveScript

    type public CosynConstraintSpec = CosynExpr

    type public CosynDirective = Directive * Location
    type public CosynFuncDefParam = OpName
    type public CosynFuncDef = CosynFuncDef' * Location
    type public CosynConstDef = CosynConstDef' * Location
    type public CosynConstraint = CosynConstraint' * Location
    type public CosynSetVar = CosynSetVar' * Location
    type public CosynMutableVar = CosynMutableVar' * Location
    type public CosynProcedure = CosynProcedure' * Location
    type public ProcedureParameter = ProcedureParameter' * Location
    type public CosynForLoop = CosynForLoop' * Location
    type public CosynWhileLoop = CosynWhileLoop' * Location
    type public DefaultValue = DefaultValue' * Location
    type public CasePattern = CasePattern' * Location
    type public 't CosynSelect = 't CosynSelect' * Location

    type public Program = CosynTopLevel list
