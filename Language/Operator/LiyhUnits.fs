namespace Liyh.Language.Operator

module rec LiyhUnits =
    open Liyh.Internal.DiagnosticKinds
    open Liyh.Internal.Diagnostics
    open System.Collections.Generic
    open System.Linq

    type public BasicDimension =
        | DTime
        | DLength
        | DMass
        | DInertiaMass
        | DElectricCurrent
        | DTemperature
        | DAmountOfSubstance
        | DLuminousIntensity
        | DNonSI of string

        override this.ToString() =
            match this with
            | DTime -> "time"
            | DLength -> "length"
            | DMass -> "mass"
            | DInertiaMass -> "inertia mass"
            | DElectricCurrent -> "electric current"
            | DTemperature -> "absolute temperature"
            | DAmountOfSubstance -> "amount of substance"
            | DLuminousIntensity -> "luminous intensity"
            | DNonSI s -> s

    let rec private arithUnitEquality (u1: UnitArith) (u2: obj) =
        match u2 with
        | :? UnitArith as u2 ->
            match u1, u2 with
            | UnitArithConstant a, UnitArithConstant b -> a = b
            | UnitArithMultiplication (a, b), UnitArithMultiplication (c, d) -> (a = c && b = d) || (a = d && b = c)
            | UnitArithDivision (a, b), UnitArithDivision (c, d) -> (a = c && b = d)
            | UnitArithPower (a, b), UnitArithPower (c, d) -> (a = c && b = d)
            | UnitArithBasicDimension a, UnitArithBasicDimension b -> a = b
            | _ -> false
        | _ -> false

    type public UnitArithConstant =
        | UnitArithConstInteger of int
        | UnitArithConstFloat of float
        | UnitArithConstWithUnit of UnitArithConstant * LiyhUnit

        override this.ToString() =
            match this with
            | UnitArithConstInteger x -> string x
            | UnitArithConstFloat x -> sprintf "%g" x
            | UnitArithConstWithUnit (cte, u) -> sprintf "%s%s" (string cte) u.symbol

    type public UnitArith =
        | UnitArithMultiplication of UnitArith * UnitArith
        | UnitArithDivision of UnitArith * UnitArith
        | UnitArithPower of UnitArith * UnitArith
        | UnitArithConstant of UnitArithConstant
        | UnitArithBasicDimension of BasicDimension
        | UnitArithUnproportional of LiyhUnit * float

        // override this.Equals arg = arithUnitEquality this arg

        override this.ToString() =
            match this with
            | UnitArithBasicDimension dim -> string dim
            | UnitArithConstant cte -> string cte
            | UnitArithMultiplication (a, b) -> sprintf "%s*%s" (string a) (string b)
            | UnitArithDivision (a, b) -> sprintf "%s/%s" (string a) (string b)
            | UnitArithPower (a, b) -> sprintf "%s**%s" (string a) (string b)
            | UnitArithUnproportional (a, b) -> sprintf "%s + %s" (string a) (string b)

    and public LiyhUnit =
        {
          /// The name of the unit is for example 'kilogram'.
          name: string

          /// The symbol of the unit is for example 'kg'.
          symbol: string

          /// The unit is for example '1000g'.
          unit: UnitArith }

    /// For example, `getDimension[4N] = getDimension[N] = MLT⁻¹`.
    let private getDimension { unit = u } = ()


    /// For example, `reduce[J⋅N] = reduce[Joule⋅Newton] = (Kg⋅m²⋅s⁻²)⋅(Kg⋅m⋅s⁻¹) = Kg²⋅m³⋅s⁻⁴`.
    let private reduce { unit = u } =

        ()

        // Envoyer ça à SumProd ?

    let public basicDimensions =
        [| "time"
           "length"
           "mass"
           "electriccurrent"
           "current"
           "temperature"
           "absolutetemperature"
           "amountofsubstance"
           "amount"
           "luminousintensity" |]

    /// Checks whether the units that have been defined are unique in terms of dimension,
    /// returns `None` if there are no errors and `Some diag` with the diagnosis if there are any.
    let private uniquenessChecking (unitList: LiyhUnit List) streamName =

        let duplicates =
            unitList
                .GroupBy(fun u -> u.unit)
                .Where(fun g -> g.Count() > 1)

        if duplicates.Count() = 0 then
            None
        else

            (* Retrieves information relevant to the error message *)

            let duplicates =
                duplicates
                |> Seq.map (fun g -> g.First().unit, Seq.map (fun u -> u.name, u.symbol) g)

            let inner (dim, names) =
                sprintf
                    "[grey53]%s[/] are [lightskyblue3_1]%s[/]"
                    (System.String.Join(", ", Seq.map fst names))
                    (string dim)

            let ulist =
                Seq.map inner duplicates
                |> fun xs -> System.String.Join(", ", xs)

            let msg1 =
                sprintf
                    "Several units that have been defined with the same dimension co-exist in the same \
                     environment, which is not encouraged because no formal relationship has been given \
                     between these units: %s.\n"
                    ulist

            let msg2 =
                let xs =
                    duplicates
                    |> Seq.toArray
                    |> Array.item 0
                    |> snd
                    |> Seq.toArray

                let u1, s1 = xs.[0]
                let u2, s2 = xs.[1]

                markupHint
                <| sprintf
                    "to illustrate, define for example [grey53]%s[/] as \
                         a multiple of [grey53]%s[/], for instance (fake value):\n\n>  unit %s, %s is %.3f %s"
                    u1 u2 u1 s1 (System.Random().NextDouble()) s2

            Some
                { isInternal = false
                  kind = DiagnosticWarning "Unit checking"
                  relevantElement = None
                  location = None
                  streamName = Some streamName
                  messages = [ msg1; msg2 ]
                  importance = Unhelpful
                  code = None }

    /// A dimensionless unit is just a scalar. For example, radians are dimensionless units.
    let public isDimensionless (unit: LiyhUnit) = false

    let private tryConvert (u1: LiyhUnit) (u2: LiyhUnit) =
        // Il faut une fonction pour isoler des variables dans des expressions UnitArith en fait.
        None

    /// In Liyh, it is possible (and recommended) to define and use units of measurement. These units are
    /// defined from the standard dimensions of the international system, the SI. The `LiyhUnits` type
    /// represents all the units that can be used in a program, and allows you to define new units, access
    /// definitions, conversions and verification associated with dimensional analysis.
    type public LiyhUnits(range: LiyhUnit list) =

        /// The list of units contains all units that are defined in a Liyh program.
        let unitList = new List<LiyhUnit>(range)

        new() = LiyhUnits([])

        /// Adds the given unit to the list of units.
        member __.AddUnit = unitList.Add

        /// Search for the given unit symbol in the list of units.
        member __.TryFind unitSymbol =
            Seq.tryFind (fun { symbol = symb } -> symb = unitSymbol) unitList

        /// Search for the given unit name in the list of units.
        member __.TryFindName unitName =
            Seq.tryFind (fun { name = name } -> name = unitName) unitList

        /// Searches for the given non-SI unit in the list of units.
        member __.TryFindNonSI unitName =
            Seq.tryFind
                (fun { unit = dim } ->
                    match dim with
                    | UnitArithBasicDimension (DNonSI id) -> id = unitName
                    | _ -> false)
                unitList

        member __.GetUnitList = unitList

        /// If one unit is defined in relation to another, then there is a conversion between them.
        member this.TryConvert unitName1 unitName2 =
            let u1 = this.TryFind unitName1
            let u2 = this.TryFind unitName2

            match u1, u2 with
            | None, _ -> None
            | _, None -> None
            | Some u1, Some u2 -> tryConvert u1 u2

        /// Checks whether the units that have been defined are unique in terms of dimension,
        /// returns `None` if there are no errors and `Some diag` with the diagnosis if there are any.
        member __.UniquenessChecking = uniquenessChecking unitList

        /// Display the list of units for debug purpose.
        member __.Show() = printfn "%A" (Seq.toList unitList)
