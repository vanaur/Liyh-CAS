namespace Liyh.Kernel.Builtin

module Data =

    module GnuPlotFormat =
        open FParsec

        let private ws =
            skipMany1Satisfy (fun c -> c = ' ' || c = '\t')

        let private pComment =
            skipString "#" >>. skipRestOfLine true >>% []

        let private pNumber = pfloat <|> (pint32 |>> float)

        let private pRow nd =
            parse {
                let! x = pNumber
                let! xs = parray nd (ws >>. pNumber) |>> Array.toList
                do! skipMany1 newline
                return x :: xs
            }

        let private pTable =
            parse {
                do! spaces

                let! y = sepBy pNumber ws
                let nd = y.Length - 1

                do! skipMany1 newline

                let! ys =
                    many (pRow nd <|> pComment)
                    |>> List.filter (not << List.isEmpty)

                return
                    y :: ys
                    |> List.map Array.ofList
                    |> Array.ofList
                    |> Array.transpose
            }

        let public readGnuPlotDataFormatOnString = runParserOnString pTable () ""

        let public readGnuPlotDataFormatOnFile path =
            runParserOnFile pTable () path System.Text.Encoding.UTF8
