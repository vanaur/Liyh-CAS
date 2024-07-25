namespace Liyh.Language.Syntax

(* Indentation library, highly inspired by https://github.com/manio143/IndentFParsec (MIT license).
   This library provides 3 main functions:

   1.  `blockOf p`, parse a list of p with the same indentation.
   2.  `greater pos p`, parses p with an indentation strictly greater than the given position.
   3.  `atLeast pos p`, parses p with an indentation greater than or equal to the given position. *)

module Indentation =
    open FParsec

    type Indent =
        | IndentAny
        | IndentExact of Position
        | IndentGreater of Position
        | IndentAtLeast of Position

        member this.toMarkup() =
            match this with
            | IndentAny -> "[lightskyblue3_1]any[/] indentation"
            | IndentGreater p -> sprintf "a [lightskyblue3_1]higher[/] indentation than the [lightskyblue3_1]%d-column[/] of the [lightskyblue3_1]%d-line[/]" p.Column p.Line
            | IndentAtLeast p -> sprintf "a [lightskyblue3_1]higher or equal[/] indentation than the [lightskyblue3_1]%d-column[/] of the [lightskyblue3_1]%d-line[/]" p.Column p.Line
            | IndentExact p -> sprintf "an [lightskyblue3_1]exact[/] indentation aligned with the last line or aligned with the %d-column" p.Column

    type public 't IndentState = { indent: Indent; userState: 't }

    type public IndentParser<'t, 'u> = Parser<'t, 'u IndentState>

    let inline public failf fmt = fail << sprintf fmt

    let private withIndentState u = { indent = IndentAny; userState = u }

    let private getIndent: IndentParser<_, _> =
        fun stream -> Reply stream.UserState.indent

    let private updateIndent newIndent : IndentParser<unit, _> =
        fun stream ->
            stream.UserState <- { stream.UserState with indent = newIndent }
            Reply Unchecked.defaultof<unit>

    let private correctIndent indent (pos: Position) =
        match indent with
        | IndentAny -> true
        | IndentExact p -> p.Column = pos.Column
        | IndentGreater p -> p.Column < pos.Column
        | IndentAtLeast p -> p.Column <= pos.Column

    let inline private parseWithIndent p =
        parse {
            let! pos = getPosition
            let! indent = getIndent

            match correctIndent indent pos with
            | true -> return! p
            | false -> return! failf "incorrect indentation, expected %s" (indent.toMarkup ())
        }

    /// Parse a line comment.
    let public lineComment symb =
        skipString symb >>? skipRestOfLine true <?> ""

    let inline private indented indent p =
        parse {
            do! updateIndent indent
            do! spaces
            return! parseWithIndent p
        }

    (* Main indentation parsers: *)

    let public any _ p = parse { return! p }
    let public exact pos = indented (IndentExact pos)
    let public greater pos = indented (IndentGreater pos)
    let public atLeast pos = indented (IndentAtLeast pos)

    let rec public blockOf p =
        parse {
            do! spaces
            let! pos = getPosition

            let! head = exact pos p
            let! tail = attempt (exact pos <| blockOf p) <|>% []

            return head :: tail
        }

    /// Applies the given parser and returns the initial and final position with the result.
    let public pWithLoc p =
        pipe3 getPosition p getPosition (fun p1 res p2 -> res, (p1, p2))

    let public runParser p u s =
        runParserOnString p (withIndentState u) "" s

    let public runParserOnFile p u path =
        runParserOnFile p (withIndentState u) path System.Text.Encoding.UTF8
