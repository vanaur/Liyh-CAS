namespace Liyh.Language.Evaluation

module LinearScan =
    open Liyh.Utils
    open System.Linq

    [<Struct>]
    type public RegisterKind =
        | KindInteger
        | KindFloat
        | KindString
        | KindSymbol

    type public Register = RegisterKind * int

    let private showReg = function
        | KindInteger, n -> sprintf "ri%d" n
        | KindFloat, n   -> sprintf "rf%d" n
        | KindString, n  -> sprintf "rs%d" n
        | KindSymbol, n  -> sprintf "re%d" n

    [<Struct>]
    type public Variable =
        { name: string
          kind: RegisterKind
          register: Register option
          stackLocation: int option
          startPoint: int
          endPoint: int }

    let public regAllocVariable name kind start close =
        { name = name; kind = kind
          register = None; stackLocation = None
          startPoint = start; endPoint = close }

    let public prettyPrintVariables variables =
        let max = (Array.maxBy (fun { endPoint = endPoint } -> endPoint) variables).endPoint

        let inner { name = name; register = reg; stackLocation = location; startPoint = start; endPoint = end' } =
            printf "  %s  " name
            printf "┃%s" (System.String(' ', start - 1))
            printf "%s" (System.String('━', end' - start))
            printf "%s┃  " (System.String(' ', max - end'))
            match location with
            | Some loc -> printf "[%d] ← %s" loc name
            | None -> printf "%s ← %s" (showReg reg.Value) name
            printf "\n"

        printf "\n"
        Array.iter inner variables

    type private Pool = Map<RegisterKind, (* spool *) int list>

    let private standardPool maxRegister =
        let t = [ 0 .. maxRegister - 1 ]
        Map.ofList [ (KindInteger, t); (KindFloat, t); (KindString, t); (KindSymbol, t) ]

    let inline private pickReg (pool: Pool) rkind =
        match pool.[rkind] with
        | [] -> failwithf "Empty register pool (kind: %A)!" rkind
        | x :: xs -> x, Map.change rkind (function _ -> Some xs) pool

    let inline private releaseReg (pool: Pool) = function
        | None -> pool
        | Some (rkind, n) ->
            let spool = pool.[rkind]
            if List.contains n spool then pool
            else Map.change rkind (function _ -> Some (n :: spool)) pool

    let inline private refresh active current pool =
        let isStillActive (var, _) = var.endPoint > current.startPoint
        let newActive, registersToRelease = List.partition isStillActive active

        let rec updatePool pool = function
            | (x, _) :: xs -> updatePool (releaseReg pool x.register) xs
            | [] -> pool

        newActive, updatePool pool registersToRelease

    let public linearScan (variables: Variable array) maxRegister =
        let mutable globalPool = standardPool maxRegister
        let mutable globalActive = List.empty
        let mutable stackLocation = 0
        let mutable result = Array.copy variables

        let inline spill active current stackLocation =
            let sorted = List.sortBy (fun ({ endPoint = endPoint }, _) -> endPoint) active

            let current, currentIndex = current
            let toSpill, toSpillIndex = List.head sorted

            if toSpill.endPoint >= current.endPoint then
                let newVariable = { current with register = toSpill.register }
                result.[toSpillIndex] <- { toSpill with register = None; stackLocation = Some stackLocation }
                result.[currentIndex] <- newVariable
                (newVariable, toSpillIndex) :: List.tail sorted
            else
                result.[currentIndex] <- { current with stackLocation = Some stackLocation }
                active

        let inline mustSpill current active =
            List.countWhen (fun ({ kind = kind }, _) -> current.kind = kind) active >= maxRegister

        for i = 0 to Array.length variables - 1 do
            let current = variables.[i]
            let currentActive, currentPool = refresh globalActive current globalPool

            let newActive, newPool =
                if mustSpill current currentActive then
                    stackLocation <- stackLocation + 1
                    spill currentActive (current, i) (stackLocation - 1), currentPool
                else
                    let newRegister, newPool = pickReg currentPool current.kind
                    let newVariable = { current with register = Some (current.kind, newRegister) }

                    result.[i] <- newVariable
                    (newVariable, i) :: currentActive, newPool

            globalActive <- newActive
            globalPool <- newPool

        result

// https://hassamuddin.com/blog/reg-alloc/

