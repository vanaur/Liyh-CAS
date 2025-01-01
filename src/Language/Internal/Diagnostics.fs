namespace Liyh.Internal

module Diagnostics =
    open System
    open Liyh.Internal.DiagnosticKinds
    open System.Collections.Generic
    open Spectre.Console

    let rec private countDigit = function
        | n when n < 10u -> 1u
        | n -> 1u + countDigit (n / 10u)

    let private showLineNumbers (currlinePos: uint) =
        let a, b, c = (currlinePos - 1u), currlinePos, (currlinePos + 1u)

        match countDigit a, countDigit b, countDigit c with
        | d1, d2, _ when d2 > d1 -> " " + string a, string b, string c
        | _, d2, d3 when d3 > d2 -> " " + string a, " " + string b, string c
        | _ when currlinePos > 1u -> string a, string b, string c
        | _ when currlinePos = 1u -> " ", string b, string c
        | _ -> " ", " ", " "

    let private showOccurred color (streamName: string option) ln col =
        sprintf "   [%s]╰╼[/] Occurred " color
        + match streamName with
          | Some path -> sprintf "in [steelblue1]%s[/]" path
          | None -> sprintf "at line [steelblue1]"
        + sprintf " at [steelblue1]%d[/]:[steelblue1]%d[/],\n\n" ln col

    let private showGreyLine = sprintf "     [grey53]%s│ %s [/]\n"
    let private showWhiteLine = sprintf "     [white]%s├ %s [/]\n"

    let private showCursorLine (atCol: int) (atLn: uint) color =
        sprintf "      %s[grey53]│%s[/][%s]↑[/]\n"
            (String(' ', int (countDigit atLn) - 1))
            (String(' ', atCol)) color

    let private showCode color (prevline: string) (currline: string) (nextline: string) atLn atCol (streamName: string option) =
        let l1, l2, l3 = showLineNumbers atLn
        let c = Console.WindowWidth

        let showLine (str: string) (ln: string) =
            if str.Length > c
            then str.Substring(0, c - 13 - ln.Length) + "[grey53]...[/]"
            else str

        new Markup(
            showOccurred color streamName atLn atCol

            + if String.IsNullOrWhiteSpace prevline then ""
              else showGreyLine l1 (showLine prevline l1)

            + if String.IsNullOrWhiteSpace currline then ""
              else showWhiteLine l2 (showLine currline l2)

            + showCursorLine atCol atLn color

            + if String.IsNullOrWhiteSpace nextline then ""
              else showGreyLine l3 (showLine nextline l3))

    let private showHeader title color =
        let header = Rule title
        header.Style <- Style.Parse color
        header.LeftAligned() |> ignore
        header

    let public correctMarkup (s: string) =
        s.Replace("[", "[[").Replace("]", "]]")

    let private reportDiagnostic (codeLines: string array) (info: DiagnosticInfo) =

        let title, color =
            match info.kind with
            | DiagnosticError ofWhat -> sprintf "%s error" ofWhat, "maroon"
            | DiagnosticWarning ofWhat -> sprintf "%s warning" ofWhat, "olive"
            | DiagnosticNote ofWhat -> sprintf "%s information" ofWhat, "dodgerblue3"
            | DiagnosticInternal ofWhat -> sprintf "Internal issue [%s]" ofWhat, "hotpink"

        let header = showHeader title color

        AnsiConsole.WriteLine()
        AnsiConsole.Write(header)

        if not (Array.isEmpty codeLines) then

            let getLn = function
                | ln when codeLines.Length < ln || ln <= 0 -> null
                | ln -> codeLines.[ln - 1] |> correctMarkup

            let ln, col, prevline, currline, nextline =
                match info.location with
                | None -> 0u, 0, null, null, null
                | Some (p, _) ->
                    let ln = int p.Line
                    uint ln, int p.Column, getLn (ln - 1), getLn ln, getLn (ln + 1)

            if not (currline = null && prevline = null && nextline = null)
            then AnsiConsole.Write(showCode color prevline currline nextline ln col info.streamName)

            printfn ""
            Seq.iter
                (fun (msg: string) ->
                    AnsiConsole.Write(
                        let p = Panel msg
                        p.Border <- BoxBorder.None
                        p.Padding <- Padding(4, 0, 4, 0)
                        p
                    ))
                info.messages
            printfn ""

    let public markupHint = sprintf "[deepskyblue1 underline]Hint[/] %s"

    let private filterByVerbosity (diagnostics: DiagnosticInfo List) (verbosity: Verbosity) =
        Seq.filter
            (fun { importance = imp } ->
                match imp with
                | Important -> verbosity = Verbosity.Level1 || verbosity = Verbosity.Level2 || verbosity = Verbosity.Level3
                | Unhelpful -> verbosity = Verbosity.Level1
                | Major -> true
                | Always -> true)
            diagnostics

    type public FileDiagnostic(codeLines: string array, filePath: string option, verbosity: Verbosity) =
        let diagnostics = List<DiagnosticInfo>()

        new(filePath: string) =
            FileDiagnostic(System.IO.File.ReadAllLines filePath, Some filePath, Verbosity.Level1)

        new(filePath: string, verbosity: Verbosity) =
            FileDiagnostic(System.IO.File.ReadAllLines filePath, Some filePath, verbosity)

        new(filePath: string, verbosity: int) =
            assert (verbosity = 1 || verbosity = 2 || verbosity = 3 || verbosity = 4)
            let verb = [ Verbosity.Level1; Verbosity.Level2; Verbosity.Level3; Verbosity.Level4 ]
            FileDiagnostic(filePath, verb.[verbosity - 1])

        member __.FileContent = String.Join('\n', codeLines)
        member __.FileLines = codeLines
        member __.FilePath = filePath
        member __.AddDiagnostic = diagnostics.Add
        member __.Repport () = Seq.iter (reportDiagnostic codeLines) (filterByVerbosity diagnostics verbosity)
