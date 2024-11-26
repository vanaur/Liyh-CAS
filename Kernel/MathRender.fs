namespace Liyh.Kernel

/// An interface for rendering and displaying *mathematical expressions* and formulas into markup languages, mainly with
/// LaTeX in mind. This module focuses on transforming abstract mathematical notations into proper visual representations.
/// Normally, by default, we try to make rendering independent of any package from the target markup language. This minilib
/// is not designed for writing documents, but only for rendering mathmode expressions.
module public rec MathRender =
    open System

    // The markup languages listed here are all only partially supported, in the sense that only the features
    // we need for math rendering in Liyh are implemented.

    [<RequireQualifiedAccess>]
    type public MarkupLanguage =
        | Latex // Default support
        | Typst
        | Mathml

    [<Struct>]
    type public TextFormat =
        | Normal    // "normal"
        | Italic    // "𝘪𝘵𝘢𝘭𝘪𝘤"
        | Bold      // "𝐛𝐨𝐥𝐝"

    [<Struct>]
    type public TextFont =
        | Normal    // "normal"
        | Mathcal   // "𝓂𝒶𝓉𝒽𝒷𝒷"
        | Mathfrak  // "𝔪𝔞𝔱𝔥𝔣𝔯𝔞𝔨"
        | Mathbb    // "𝕞𝕒𝕥𝕙𝕓𝕓"

    [<Struct>]
    type public Size =
        | Tiny          // 5pt
        | Scriptsize    // 7pt
        | Footnotesize  // 8pt
        | Small         // 9pt
        | Normal        // 10pt
        | Large1        // 12pt
        | Large2        // 14.4pt
        | Large3        // 17.28pt
        | Huge1         // 20.74pt
        | Huge2         // 24.88pt

    type public Text =
        { text: string
          format: TextFormat option // default: `Normal`
          font: TextFont option     // default: `Normal`
          size: Size option }       // default: `Normal`

    [<Struct>]
    type public ScriptKind =
        | SuperScript   // "Aᵃ"
        | SubScript     // "Aₐ"

    type public Script =
        { content: MathRender
          kind: ScriptKind
          spaced: bool }        // add space before the script?

    [<Struct>]
    type public BetweenKind =
        | Custom of left: string * right: string
        | Parentheses   // ( )
        | Brackets      // [ ]
        | Braces        // { }

    type public Between =
        { content: MathRender
          kind: BetweenKind }

    [<Struct>]
    type public Space =
        | Normal     // equivalent of space in normal text
        | Quad       // 18mu
        | QQuad      // 36mu
        | Space1     // 3mu
        | Space2     // 4mu
        | Space3     // 5mu
        | AntiSpace  // -3mu

    /// Represents elements that are too dependent on the target markup language to be built with the
    /// elementary bricks of `MathRender`. For example roots or fractions.
    type public Command =
        | Frac of MathRender * MathRender
        | Sqrt of MathRender
        | Root of MathRender * MathRender
        | Abs of MathRender
        | Mat of MathRender array2d
        | Leq   // ≤
        | Geq   // ≥
        | Neq   // ≠

    /// Abstract markup langage to interface with real ones. Please use utilities instead of constructors.
    type public MathRender =
        | Text of Text              // Text in mathmode
        | Symbol of string          // A simple raw string, for example `x` or `+`
        | Script of Script          // Superscript, subscript or prescript
        | Group of MathRender list  // Syntactic elements grouped together in a structure (`{...}` in Latex for example)
        | Between of Between        // Math between symbols, for example parens or braces
        | Command of Command        // An element that is invoked with arguments, for example `frac{...}{...}`
        | Space of Space            // Space in mathmode
        | Nothing                   // No element

        /// Converts the `MathRender` abstract representation into a string corresponding to the specified markup language.
        member public this.Compile (markup: MarkupLanguage) = compile this markup

        /// Converts the `MathRender` abstract representation into a Latex string.
        member public this.Compile () = compile this MarkupLanguage.Latex

        /// Used to group two elements side by side.
        static member ( ++ ) (left: MathRender, right: MathRender) =
            match left, right with
            | Group xs, Group ys -> MathRenderHelper.group (xs @ ys)
            | Group xs, y -> MathRenderHelper.group (xs @ [ y ])
            | x, Group ys -> MathRenderHelper.group (x :: ys)
            | _ -> MathRenderHelper.group [ left; right ]

    /// This module provides utilities for composing `MathRender` expressions, often in a more optimized and/or convenient
    /// way than using `MathRender` constructors alone. We recommend using this module instead.
    [<RequireQualifiedAccess>]
    module public MathRenderHelper =

        /// Text with default settings.
        let inline public simpleText (text: string) =
            Text
                { text = text
                  format = None
                  font = None
                  size = None }

        /// Symbol with default settings.
        let inline public symbol (symbol: string) =
            Symbol symbol

        let inline public number (num: double) =
            symbol (sprintf "%.15g" num)

        /// Superscript with default settings.
        let inline public superscript (content: MathRender) =
            Script
                { content = content
                  kind = SuperScript
                  spaced = false }

        /// Subscript with default settings.
        let inline public subscript (content: MathRender) =
            Script
                { content = content
                  kind = SubScript
                  spaced = false }

        /// Syntactic elements grouped together (this function is used to flatten groupings whenever possible)
        let rec public group (content: MathRender list) =
            match List.filter (( <> ) Nothing) content with
            | Group xs :: ys when not (List.isEmpty ys) ->

                let flattenedYs =
                    match group ys with
                    | Group ys' -> ys'
                    | y -> [ y ]

                Group(xs @ flattenedYs)
            | [ x ] -> x
            | content -> Group content

        /// An element `b` raised to the power `p`.
        let inline public power (b: MathRender) (p: MathRender) =
            b ++ superscript p

        /// Between parentheses.
        let inline public parens (content: MathRender) =
            Between
                { content = content
                  kind = Parentheses }

        /// Between brackets.
        let inline public brackets (content: MathRender) =
            Between { content = content; kind = Brackets }

        /// Between braces.
        let inline public braces (content: MathRender) =
            Between { content = content; kind = Braces }

        (* -- functions -- *)

        let inline public frac (num: MathRender) (den: MathRender) =
            Command(Command.Frac(num, den))

        let inline public sqrt (content: MathRender) =
            Command(Command.Sqrt content)

        let inline public root (x: MathRender) (b: MathRender) =
            Command(Command.Root(x, b))

        let inline public abs (content: MathRender) =
            Command(Command.Abs content)
        
        let inline public mat (content: MathRender array2d) =
            Command(Command.Mat content)

        let inline public func (name: string) (arguments: MathRender list) =
            simpleText name ++ parens (List.reduce (fun acc a -> acc ++ symbol "," ++ a) arguments)

        let inline public log (x: MathRender) (b: MathRender) =
            simpleText "log" ++ subscript b ++ parens x

        let inline public ln (x: MathRender) =
            simpleText "log" ++ parens x

        (* -- symbols -- *)

        let public leq = Command.Leq
        let public geq = Command.Geq
        let public le = symbol "<"
        let public ge = symbol ">"
        let public neq = Command.Neq
        let public plus = symbol "+"
        let public minus = symbol "-"
        let public cdot = symbol "⋅"

        let public nothing = Nothing

    /// Handle latex rendering from `MathRender`.
    [<RequireQualifiedAccess>]
    module public MathRenderLatex =

        let private compileSize =
            function
            | Size.Tiny -> @"\tiny"
            | Size.Scriptsize -> @"\scriptsize"
            | Size.Footnotesize -> @"\footnotesize"
            | Size.Small -> @"\small"
            | Size.Large1 -> @"\large"
            | Size.Large2 -> @"\Large"
            | Size.Large3 -> @"\LARGE"
            | Size.Huge1 -> @"\huge"
            | Size.Huge2 -> @"\Huge"
            | _ -> ""

        let private compileSpace =
            function
            | Normal -> @"\ "
            | Quad -> @"\quad"
            | QQuad -> @"\qquad"
            | Space1 -> @"\,"
            | Space2 -> @"\:"
            | Space3 -> @"\;"
            | AntiSpace -> @"\!"

        /// Compiles the given abstract math render to a Latex equivalent.
        let rec public compile =
            function
            | Text txt -> compileText txt
            | Symbol s -> s
            | Script script -> compileScript script
            | Space space -> compileSpace space
            | Group group -> compileGroup group
            | Between between -> compileBetween between
            | Command command -> compileCommand command
            | Nothing -> ""

        and private compileText (text: Text) =
            let format =
                match Option.defaultValue TextFormat.Normal text.format with
                | TextFormat.Bold -> @"\pmb"
                | TextFormat.Italic -> @"\mathit"
                | TextFormat.Normal -> ""

            let font =
                match Option.defaultValue TextFont.Normal text.font with
                | TextFont.Mathbb -> @"\mathbb"
                | TextFont.Mathcal -> @"\mathcal"
                | TextFont.Mathfrak -> @"\mathfrak"
                | TextFont.Normal -> ""

            let size = compileSize (Option.defaultValue Size.Normal text.size)

            [ format; font; size ]
            |> List.filter (not << String.IsNullOrEmpty)
            |> function
                | [] -> sprintf @"\text{%s}" text.text
                | formats ->
                    List.fold (fun acc fmt -> sprintf @"%s{%s}" fmt acc) (sprintf @"\text{%s}" text.text) formats

        and private compileScript (script: Script) =
            let space = if script.spaced then "{}" else ""

            let su =
                match script.kind with
                | ScriptKind.SubScript -> @"_"
                | ScriptKind.SuperScript -> @"^"

            let content = compile script.content

            sprintf @"%s%s{%s}" space su content

        and private compileGroup (group: MathRender list) =
            "{" + List.fold (fun acc a -> acc + compile a) "" group + "}"

        and private compileBetween (between: Between) =
            let spaced =
                match between.kind with
                | BetweenKind.Custom _ -> " "
                | _ -> ""

            let left, right =
                match between.kind with
                | BetweenKind.Braces -> @"\left{", @"\right}"
                | BetweenKind.Brackets -> @"\left[", @"\right]"
                | BetweenKind.Parentheses -> @"\left(", @"\right)"
                | BetweenKind.Custom(l, r) -> l, r // may not work depending the markup actually...

            left + spaced + (compile between.content) + spaced + right

        and private compileCommand =
            function
            | Command.Frac(a, b) -> sprintf @"\frac{%s}{%s}" (compile a) (compile b)
            | Command.Sqrt a -> sprintf @"\sqrt{%s}" (compile a)
            | Command.Root(a, b) -> sprintf @"\sqrt[%s]{%s}" (compile b) (compile a)
            | Command.Abs a -> sprintf @"\left|{%s}\right|" (compile a)
            | Command.Mat a -> compileMat a
            | Command.Leq -> @"\leq"
            | Command.Geq -> @"\geq"
            | Command.Neq -> @"\neq"

        and private compileMat (mat: MathRender array2d) =
            let cs = Array2D.map compile mat
            let rows = [| for row in 0 .. Array2D.length1 cs - 1 -> cs.[row, *] |]
            let rows = Array.map (fun (c: string array) -> System.String.Join(" & ", c)) rows

            let env = sprintf @"\begin{bmatrix} %s \end{bmatrix}"
            let body = System.String.Join(@" \\ ", rows)

            env body

    /// Handle typst rendering from `MathRender`.
    [<RequireQualifiedAccess>]
    module public MathRenderTypst =

        let private compileSize =
            function
            | _ -> "" // not supported

        let private compileSpace =
            function // 1mu = 1em/18
            | Normal -> @" "
            | Quad -> @"#h(18em/18)"
            | QQuad -> @"#h(36em/18)"
            | Space1 -> @"#h(3em/18)"
            | Space2 -> @"#h(4em/18)"
            | Space3 -> @"#h(5em/18)"
            | AntiSpace -> @"#h(-3em/18)"

        /// Compiles the given abstract math render to a Latex equivalent.
        let rec public compile =
            function
            | Text txt -> compileText txt
            | Symbol s -> s
            | Script script -> compileScript script
            | Space space -> compileSpace space
            | Group group -> compileGroup group
            | Between between -> compileBetween between
            | Command command -> compileCommand command
            | Nothing -> ""

        and private compileText (text: Text) =
            let format =
                match Option.defaultValue TextFormat.Normal text.format with
                | TextFormat.Bold -> @"bold"
                | TextFormat.Italic -> @"italic"
                | TextFormat.Normal -> ""

            let font =
                match Option.defaultValue TextFont.Normal text.font with
                | TextFont.Mathbb -> @"bb"
                | TextFont.Mathcal -> @"cal"
                | TextFont.Mathfrak -> @"frak"
                | TextFont.Normal -> ""

            let size = compileSize (Option.defaultValue Size.Normal text.size)

            [ format; font; size ]
            |> List.filter (not << String.IsNullOrEmpty)
            |> function
                | [] -> sprintf "\"%s\"" text.text
                | formats ->
                    List.fold (fun acc fmt -> sprintf @"%s(%s)" fmt acc) (sprintf "\"%s\"" text.text) formats

        and private compileScript (script: Script) =
            let space = if script.spaced then " #h(0pt) " else ""

            let su =
                match script.kind with
                | ScriptKind.SubScript -> @"_"
                | ScriptKind.SuperScript -> @"^"

            let content = compile script.content

            sprintf @"%s%s(%s)" space su content

        and private compileGroup (group: MathRender list) =
            List.fold (fun acc a -> acc + compile a) "" group

        and private compileBetween (between: Between) =
            let spaced =
                match between.kind with
                | BetweenKind.Custom _ -> " "
                | _ -> ""

            let left, right =
                match between.kind with
                | BetweenKind.Braces -> "{", "}"
                | BetweenKind.Brackets -> "[", "]"
                | BetweenKind.Parentheses -> "(", ")"
                | BetweenKind.Custom(l, r) -> l, r // may not work depending the markup actually...

            left + spaced + (compile between.content) + spaced + right

        and private compileCommand =
            function
            | Command.Frac(a, b) -> sprintf @"frac(%s, %s)" (compile a) (compile b)
            | Command.Sqrt a -> sprintf @"sqrt(%s)" (compile a)
            | Command.Root(a, b) -> sprintf @"root(%s, %s)" (compile b) (compile a)
            | Command.Abs a -> sprintf @"abs(%s)" (compile a)
            | Command.Mat a -> compileMat a
            | Command.Leq -> @"lt.eq"
            | Command.Geq -> @"gt.eq"
            | Command.Neq -> @"eq.not"

        and private compileMat (mat: MathRender array2d) =
            let cs = Array2D.map compile mat
            let rows = [| for row in 0 .. Array2D.length1 cs - 1 -> cs.[row, *] |]
            let rows = Array.map (fun (c: string array) -> System.String.Join(", ", c)) rows

            let env = sprintf @"\begin{bmatrix} %s \end{bmatrix}"
            let body = System.String.Join(@"; ", rows)

            env body

    /// Handle mathml rendering from `MathRender`.
    [<RequireQualifiedAccess>]
    module public MathRenderMathML =

        let private compileSize =
            function
            | _ -> "" // not supported

        let private compileSpace =
            function
            | _ -> "" // not supported

        /// Compiles the given abstract math render to a Latex equivalent.
        let rec public compile =
            function
            | Text txt -> compileText txt
            | Symbol s -> sprintf "<mi>%s</mi>" s
            | Script script -> compileScript script
            | Space space -> compileSpace space
            | Group group -> compileGroup group
            | Between between -> compileBetween between
            | Command command -> compileCommand command
            | Nothing -> ""

        and private compileText (text: Text) =
            sprintf "<mo>%s</mo>" text.text

        and private compileScript (script: Script) =
            let space = if script.spaced then "<mo>&#xA0;</mo>" else ""

            let su1, su2 =
                match script.kind with
                | ScriptKind.SubScript -> "<msub>", "</msub>"
                | ScriptKind.SuperScript -> "<msup>", "</msup>"

            let content = compile script.content

            sprintf @"%s%s<none></none><mrow>%s</mrow>%s" space su1 content su2

        and private compileGroup (group: MathRender list) =
            "<mrow>" + List.fold (fun acc a -> acc + compile a) "" group + "</mrow>"

        and private compileBetween (between: Between) =
            let spaced =
                match between.kind with
                | BetweenKind.Custom _ -> "<mo>&#xA0;</mo>"
                | _ -> ""

            let left, right =
                match between.kind with
                | BetweenKind.Braces -> "<mrow><mo>{</mo>", "<mo>}</mo></mrow>"
                | BetweenKind.Brackets -> "<mrow><mo>[</mo>", "<mo>]</mo></mrow>"
                | BetweenKind.Parentheses -> "<mrow><mo>(</mo>", "<mo>)</mo></mrow>"
                | BetweenKind.Custom(l, r) -> $"<mrow><mo>{l}</mo>", $"<mo>{r}</mo></mrow>"

            left + spaced + (compile between.content) + spaced + right

        and private compileCommand =
            function
            | Command.Frac(a, b) -> sprintf "<mfrac><mrow>%s</mrow><mrow>%s</mrow></mfrac>" (compile a) (compile b)
            | Command.Sqrt a -> sprintf "<msqrt>%s</msqrt>" (compile a)
            | Command.Root(a, b) -> sprintf "<mroot><mrow>%s</mrow><mrow>%s</mrow></mroot>" (compile b) (compile a)
            | Command.Abs a -> sprintf "<mrow><mo>|</mo>%s<mo>|</mo></mrow>" (compile a)
            | Command.Mat a -> compileMat a
            | Command.Leq -> "<mo>&#x2264;</mo>"
            | Command.Geq -> "<mo>&#x2264;</mo>"
            | Command.Neq -> "<mo>&#x2260;</mo>"

        and private compileMat (mat: MathRender array2d) =
            let cs = Array2D.map compile mat

            let rows = Array2D.length1 cs
            let cols = Array2D.length2 cs

            let rowsToMathML =
                [for i in 0 .. rows - 1 ->
                    let row =
                        [ for j in 0 .. cols - 1 -> $"<mtd><mi>{cs.[i, j]}</mi></mtd>" ]
                        |> String.concat ""
                    $"<mtr>{row}</mtr>"]
                |> String.concat ""

            $"<mtable>{rowsToMathML}</mtable>"

    let inline private texEnclose s = "$" + s + "$"
    let inline private mathmlEnclose s = "<math xmlns=\"http://www.w3.org/1998/Math/MathML\">" + s + "</math>"

    /// Converts the `MathRender` abstract representation into a string corresponding to the specified markup language.
    let public compile (mathrender: MathRender) =
        function
        | MarkupLanguage.Latex -> texEnclose (MathRenderLatex.compile mathrender)
        | MarkupLanguage.Typst -> texEnclose (MathRenderTypst.compile mathrender)
        | MarkupLanguage.Mathml -> mathmlEnclose (MathRenderMathML.compile mathrender)
