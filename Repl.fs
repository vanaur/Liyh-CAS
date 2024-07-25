namespace Liyh

module rec REPL =
    open Binarysharp.Benchmark
    open PrettyPrompt.Highlighting
    open PrettyPrompt
    open Liyh.Language.Syntax.Cosyn
    open Liyh.Language.Syntax.Parser
    open Liyh.Language.Syntax.Indentation
    open Liyh.Kernel.SumProd
    open Liyh.Language.Absyn

    open FParsec
    open System

    let private header =
        """
        __    _       __
       / /   (_)_  __/ /_
      / /   / / / / / __ \     Version 0.1.0 — EARLY-DEV
     / /___/ / /_/ / / / /     https://github.com/vanaur/liyh
    /_____/_/\__, /_/ /_/      Type !h for help
            /____/

    Liyh is a general purpose computer algebra system that can be used from its own language.
    It is used in REPL, but is much more suitable in its graphical environment, to access the
    graphical environment of Liyh (in your browser), type !lge

    In the meantime, you can enter expressions to be evaluated here!

    """

    let private helpText =
        """

    ➤  !help !h <COMMAND or NAME> ............. Display the help associated with the given name ;
    ➤  !quit !q ............................... Exits the REPL ;
    ➤  !clear !cls ............................ Clear the terminal ;
    ➤  !load !l <FILE> ........................ Load a Liyh program and execute it ;
    ➤  !bench !b <EXPR or FILE> ............... Performs a benchmark on the given programme ;
    ➤  !rep !r <NBR> <EXPR> ................... Repeats NBR times the EXPR.

        """

    type private Command =
        | InlineExpr of CosynExpr
        | Bench of Bench
        | Help of string
        | Load of string
        | Repeat of int * CosynExpr
        | Clear
        | Quit
        | Nothing

    and private Bench =
        | BenchExpr of CosynExpr
        | BenchFile of string

    let private pQuit =
        choice [ skipStringCI "quit"
                 skipStringCI "q" ]
        >>% Quit

    let private pClear =
        choice [ skipStringCI "clear"
                 skipStringCI "cls" ]
        >>% Clear

    let private pHelp =
        choice [ skipStringCI "help"
                 skipStringCI "h" ]
        >>. spaces
        >>. restOfLine true
        |>> Help

    let private pLoad =
        choice [ skipStringCI "load"
                 skipStringCI "l" ]
        >>. spaces
        >>. restOfLine true
        |>> Load

    let private pBench =
        choice [ skipStringCI "bench"
                 skipStringCI "b" ]
        >>. spaces
        >>. pExpr
        |>> BenchExpr |>> Bench

    let private pRepeat =
        choice [ skipStringCI "repeat"
                 skipStringCI "r" ]
        >>. pipe2
            (spaces >>. pint32)
            (spaces >>. pExpr)
            (fun a b -> Repeat(a, b))

    let private pInlineExpr = spaces >>. pExpr .>> eof |>> InlineExpr

    let private pCommand =
        attempt (
            between
                spaces
                spaces
                (skipChar '!'
                 >>. choice [ pQuit   <?> "quit"
                              pHelp   <?> "help"
                              pClear  <?> "clear"
                              pLoad   <?> "load"
                              pBench  <?> "bench"
                              pRepeat <?> "repeat" ]))

        <|> (pInlineExpr <?> "a liyh expression")

    let private handleHelp (text: string) =
        if text.Trim() = "" then printfn "%s" helpText

    let private handleLoad (path: string) =
        if IO.File.Exists path then printfn "The path exisst"
        else printfn "The file `%s` was not found." path

    let private handleClear () =
        Console.Clear()
        printfn "%s" header

    let private handleQuit () =
        printfn "\nBye bye."
        exit 0

    let private handleBench (nbr: int) (expr: CosynExpr') =
        let shark = BenchShark()
        let sp = cosynToSumProd expr
        let watch = Diagnostics.Stopwatch.StartNew()
        let res = shark.EvaluateTask(Action(fun _ -> ignore (simp sp)), uint nbr)
        watch.Stop()
        printfn "\n[Performed %d tests: avg %g ms tot %d ms]" nbr res.AverageExecutionTime.TotalMilliseconds watch.ElapsedMilliseconds
        handleInlineExpr expr

    let private handleInlineExpr (expr: CosynExpr') =
        Console.ForegroundColor <- ConsoleColor.Cyan
        printfn "\n%s\n" (simp (cosynToSumProd expr)).ToLatex
        Console.ResetColor ()

    let private handleCommand = function
        | Help text -> handleHelp text
        | Load path -> handleLoad path
        | Clear -> handleClear ()
        | Quit -> handleQuit ()
        | Bench (BenchExpr (expr, _)) -> handleBench 50 expr
        | Repeat (nbr, (expr, _)) -> handleBench nbr expr
        | InlineExpr (expr, _) -> handleInlineExpr expr
        | _ -> ()

    let public startREPL () =
        printfn "%s" header

        let pconfig =
            PromptConfiguration(
                prompt = FormattedString(" :  "),
                selectedTextBackground = AnsiColor.Cyan,
                tabSize = 3)

        let prompt = Prompt(configuration = pconfig)

        while true do
            let input = prompt.ReadLineAsync()

            match runParser (pCommand <|>% Nothing) () input.Result.Text with
            | Success (res, _, _) -> handleCommand res
            | Failure (msg, _, _) -> printfn "\n%s\n" msg
