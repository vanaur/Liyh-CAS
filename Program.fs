#nowarn "3391"
#nowarn "25"

open Binarysharp.Benchmark
open System
open System.IO
open Plotly.NET
open System.Collections
open System.Linq
open Liyh.Utils
open Liyh.Language.Syntax.Parser
open FParsec
open Liyh.Kernel
open Liyh.Language.Evaluation.IL
open Liyh.Language.Evaluation.ILParser
open Liyh.Language.Evaluation.VirtualMachine
open Liyh.Language.Evaluation.Hex
open Liyh.Language.Evaluation.LinearScan
open System.ComponentModel
open Liyh.Kernel
open ByteDev.Encoding
open Liyh.Kernel.Prime


//match compileFile "test.lysm" with
//| Some program ->
//    let vm = new LiyhVM(program)
//    vm.Run()
//    printfn "\n[Done in %g milliseconds]" vm.ExecutionTime.TotalMilliseconds
//| None -> ()
//

// noice: I simply put a unique id on each node and have auxiliary information in a hash map. Worked well for me so far.
// comme ça on met les informations dans un hashmap :open_mouth:


let sp' text =
    match startExprParser text with
    | Success (res, _, _) -> Liyh.Language.Absyn'.Absyn.cosynExprToSymbolic res
    | _ -> raise (Exception "BOOM")


// let diag = Liyh.Internal.Diagnostics.FileDiagnostic("./test.ly") //Liyh.Internal.Diagnostics.FileDiagnostic("test.ly")
// let r = startParser diag
// diag.Repport ()

// printfn "%A" r

// let shark = BenchShark()
// let res = shark.EvaluateTask(Action(fun _ -> ignore (simp sp)), uint nbr)
// printfn "%gms" res.AverageExecutionTime.TotalMilliseconds

let inline bench ([<InlineIfLambda>] fn) n =
    let shark = BenchShark()
    let task = Action fn
    let res = shark.EvaluateTask(task, uint n)
    printfn "[%d runs] %gms." n res.AverageExecutionTime.TotalMilliseconds

//      // --------- ON EN ETAIT ICI ------------ //
//      let a = toSumPow <| sp' "6b + 2a + 1 + 3c"
//      //let a = toSumPow <| sp' "8a + (1/4) * (6 + 2a)"
//      // let a = toSumPow <| sp' "2*(1 + 4*x) + (1 + x)*(1 + 4*x) + 2*(1 + x)"
//      let s = Simplification.simplify a
//      printfn "\n_________\n%s = %s" (toLatex a).Value (toLatex s).Value
//      
//      
//      printfn "%A" <| primeFactorDecompose 56

let generateUnivPoly n v =
    let rnd = Random()
    List.init n (fun _ -> Term [powId (SumPow.SumPow.Const(rnd.Next(1, n))); Pow(v, SumPow.SumPow.Const(rnd.Next(1, n)))]) |> Sum

let generateMultivPoly n (vs: SumPow list) =
    let rnd = Random()
    List.init n (fun _ -> Term [powId (SumPow.SumPow.Const(rnd.Next(1, n))); Pow(vs.[rnd.Next(0, vs.Length)], SumPow.SumPow.Const(rnd.Next(1, n)))]) |> Sum

// A faire:
//      [✓] simpPureConst
//      [✓] opérations sur les polynômes
//      [✓] la partie non-poly et la partie poly des polynômes
//      [✓] les polynômes multivariés
//      [ ] dans le retriveDegree, `PureConstantInteger` est *supposé*, mais il échoue en x^t par exemple.
//      [✓] adaptWrt ≡ reorder
//      [✓] fromIntegerRoots (déjà fait dans SumProd)
//      [✓] "bug" du fixedPoint => En plus ça améliore les performances !!
//      [✓] à la ligne `let cpart' = Sum [ Term cpart ] |> Simplification.simplify` on aimerait se débarasser de la simplification
//          pour la déléguer à la ligne d'après, mais cela ne marche pas (càd la ligne d'après ne simplifie pas...)
//          le problème vient probablement de Simplification.simplify qui ne gère pas un truc...
//          cela dit, ça améliore magiquement les performances.
//      [✓] /!\ `PureConstantInteger` renvoie en effet un entier, mais ne vérifie pas que l'expression constante
//          est effectivement entière ! Par exemple `3.2` sera match mais renvoyé par `3`.
//      [✓] dans la construction d'un polynôme multivarié, il faut effectuer une vérification de si le polynôme final
//          ne manque d'aucune des variales données, si c'est le cas alors on peut simplifier sa représentation.
//      [ ] List.areEquivalent ne marche pas
//      [✓] Réécrire `toSumPow` pour éliminer les exposants nuls
//      [×] `Map.join` est en fait vraiment lent -> c'est le plus efficace possible
//      [ ] Il faudrait implémenter une version de la multiplication polynômiale spécialisée pour les coefficients numériques
//          et qui serait du coup bien plus rapide que pour les coefficients généraux
//      [ ] il faudrait clean `clean`, en plus ça marche pas:
//          let p1, _ = (toSumPow << sp') "3*x*y + 2*x + 6*a + 1" |> Polynomial.asMultivariatePolynomial [ Name "x"; Name "a"; Name "y" ] List.empty
//          let p2, _ = (toSumPow << sp') "a + 18*x + 9" |> Polynomial.asMultivariatePolynomial [ Name "a"; Name "x"; Name "p" ] List.empty
//          let a = Polynomial.toSumPow (Polynomial.clean <| p1 * p2)
//          REM: en fait, il est beaucoup plus facile d'implémenter `clean` en passant par `toSumPow` qui élimine
//          les variables fantômes ! Ca sera pas trop lent en plus.
//      [ ] gérer "the excluded variable is a variable"
//      [✓] `subst` marche pas dans Polynomial
//      [ ] toSumPow devrait ne pas considérer les coefficients nuls
//      [ ] Polynomial.evaluate est très lent par rapport à SumPow. Ca devrait être optimisé puisque c'est une
//          représentation spécialisée...
//      [?] (a/b/(c*a))*(c*d/a)/d → 1/(a*b)
//      [ ] Améliorer la case | SumPow.Const a, SumPow.Const b when b > 0 -> SumPow.Const(a ** b) dans `power`...
//      [✓] Expand est en fait fragile car il peut boucler à l'infini (voir la ligne commenté)
//      [ ] Multiplié par -1 c'est chiant quand il y a déjà une constante dans l'expression
//      [ ] Le hash de sumpow marche pas ou jsp, mais `memoize` nous ennuie...... C'est très grave !!
//      [✓] Il faudrait `expand` les fractions aussi
//      [ ] `clean` est important pour créer un polynôme univarié à partir d'un truc multivarié mais qui n'utilise qu'une Variable
//          on devrait l'utiliser dans `Numeric`
//      [ ] il faudrait rajouter une variable `i` pour l'unité imaginaire
//      [✓] `distribute` c'est de la turbo-merde ça marche pas et c'est à chier
//      [ ] `isPolynomialCandiat` n'est pas fiable.
//      [ ] dans `power'` il faudrait mieux gérer le cas des fractions.
//      [ ] il faudrait faire pareil que `ProdWith` avec les sommes.
//      [ ] le bout de code
//              result
//              |> Map.toList
//              |> List.map (
//                  Term
//                  << function
//                      | key, One -> flattenTerm key
//                      | key, value -> flattenTerm (powId value :: key))
//              |> Sum
//              // |> flatten
//          dans `simpSum` devrait être amélioré pour tennir compte de la flattenization... (exemple: A - B/2)
//      [ ] dans les opérations arithmétiques élémentaires pour les constantes, à part pour la division (et l'exposant négatif)
//          on calcul tout numériquement sauf le calcul dépasse la précision du double.
//      [ ] se débarasser de Plotly.NET et utiliser ScottPlot. Est-ce que ScottPlot fait du 3D?
//      [ ] faire une fonction qui évalue une fonction complexe numériquement en générant des points réels et imaginaires
//      [ ] il faudrait factoriser un peu `SumPow.fs` et mettre des trucs dans d'autres fichiers, non ? Typiquement, on a besoin
//          de la factorisation, ce qui se fait via les polynômes. Et `reduce` aussi.
//          Parce que `ElemFun` ~ `Complex` ~ `ElemFun` ~ `Reduce` ~ `Polynomial` ~ `SumPow`.
//      [ ] SumPow.Simplify ne gère pas
//              - n(a + b) / (a + b)    |
//              - n*(a + b) + (a + b)   -> car `n` n'est pas une constante (=> normal, simplify ne gère pas ce style de cas)
//                                      => reduce devrait arriver à faire ça.
//      [?] Changer le nom de `simplify` en `fastSimplify` ? Parce que les cas précédents sont triviaux quand même.
//      [ ] Le LaTeX c'est toujours pas ça... Par exemple : "3 * (a + b) / (a + 1 + b - 1)**2".
//      [✓] Il faudrait mettre `excludedVariables` dans la structure du polynôme, parce que si on veut le reconstruire par la suite
//          et qu'il contient des variables à exclure bah on peut pas.
//      [∘] Modifier toutes les mauvaises assertions par des exception.
//      [✓] Créer un module spécifique pour les bases de Groebner.
//      [ ] Définir une fonction de création d'idéal polynomial. C'est cet idéal qu'on pourrait également passer
//          dans |Polynomial| et tout. Ou alors on ne le fait pas ?
//      [ ] Ajouter `reduce` à la division et renvoyer, selon le dénominateur, un nouveau polynôme ou alors une fraction polynomiale.
//      [ ] La ligne `let (p :: fs) = compatibles (p :: fs)` dans `reduce` est dangeureuse puisque `compatibles` ne renvoie peut-être
//          pas forcément la liste dans le même ordre.
//      [ ] Rajouter une option dans les patterns polynomiaux pour voir si une variable compte comme un polynôme
//      [ ] Il faudrait vraiment définir une grosse fonction heuristique pour déterminer si une expression vaut 0
//      [ ] Dans `isSquareFree` if FAUT donner la variable.
//      [ ] La division longue pour doubles renvoie un résultat approximatif, il faudrait des fractions.
//      [ ] Longue division quand le dénominateur > numérateur : https://www.wolframalpha.com/input?i=remainder+of+%28x%C2%B2+%2B+1%29+%2F+%284x%E2%81%B8+%2B+3x%C2%B3+%2B+2%29
//      [ ] Implémenter la pseudo-division polynomiale (voir livre)
//      [ ] !!! x**3 - 6*(x**2) + 11**x - 6 a été parsé comme un polynôme !!!
//      [ ] Virer SumProd

// let a = (toSumPow << sp') "Exp[i * pi / 2]"
// printfn "%A" a
// printfn "%A" (Complex.isImaginaryUnit a)

// Il faudrait faire la factorisation... C'est un truc vraiment important.

// let a = (toSumPow << sp') "Cos[3] + (Cos[pi/2] + Exp[pi * ((i**5)*Sin[pi/2] + Cos[pi/2]) / 2]*Sin[pi/2])*Sin[3]"
// match a with
// | Complex.Cis arg -> printfn "yes: %s" (toLatexValue arg)
// | _ -> printfn "nope"

// let a = (toSumPow << sp') "3*x + 2*x*y"
// let z = FastFactorize.fastFactorize a

//      let a = (toSumPow << sp') "4*i + 3" // todo? => pour faire ça efficacement, il faut la factorisation...
//      let z = Complex.asComplex a
//      printfn "%A" z


let vs = [ Name "a"; Name "b"; Name "c"; Name "d"; Name "e"; Name "f" ]
let vs' = [ Name "x"; Name "y"; Name "z" ]

// let f1, _ = (toSumPow << sp') "(x**2)*(y**2) + x + y" |> Polynomial.Pattern.asMultivariatePolynomial vs' []
// let f2, _ = (toSumPow << sp') "x*y" |> Polynomial.Pattern.asMultivariatePolynomial vs' []

let inner (xs: string list) =
    [ for x in xs -> let f, _ = (toSumPow << sp') x |> Polynomial.Pattern.asMultivariatePolynomial vs' [] in f ]

let fs =
    inner [
        // ici:
        // "y+1"
        // "x**2 + 1"
        // "x*(y**2) - 1"

        // "x**3 - 2*x*y"
        // "(x**2)*y - 2*(y**2) + x"

        // "(x**2)*y + x*(y**2) + y**2"
        // "y**2 - 1"
        // "x*y - 1"

        // "x**2 + 1"
        // "x*(y**2) - 1"

        "2*x + y"
        "y - x**2"
        "x + y"

        // "x**2 - y"
        // "1 - x"
        // "y + 1"
        // "x**2 + 1"
        // "x*(y**2) - 1"

        // "x*(y**2) + 1"
        // "x*y + 1"
        // "y + 1"

        // "(x**2)*(y**2) + x + y"
        // "x*y"

        // "(x**3)*(y**2) + x*y + x"
        // "y**2 + 1"
        // "x*y + 1"
    ]

// let groebnerBasis = Polynomial.GroebnerBasis.computeGroebnerBasis fs
// List.iter (toLatexValue >> printfn @"%s") groebnerBasis

//let a = (toSumPow << sp') "1/2/(3+1/2)/4/(3/(1 + 1/2)) * (1 - 1/2) + Root[27, 3] + Sqrt[8]" //"Sqrt[1/2] * Sqrt[3/4]"
let a = (toSumPow << sp') "Sqrt[1/2] * Sqrt[3/2]"
//let a = (toSumPow << sp') "1/2 + Cos[2] + 3/4 + 5/6"
//let a = (toSumPow << sp') "Sqrt[8]"
let z = PureConstantExpression.csimplify a
//printfn "%A" z
printfn "\n-----\n%s = \n%s" (toLatexValue a) (toLatexValue z)

// let z' = (inner [ "6*(x**2)*y*(z**3) + 4*(x**5)*y*z + 2*(x**4)*(y**2)*z" ]).Head
// let factor, p = Polynomial.Factorization.termFactoringWRT z' (Name "x")
// printfn @"%s = %s\cdot\left(%s\right)" (toLatexValue z') (toLatexValue factor) (toLatexValue p)


// --------------------------------
// Square-free factorization:
// x**4 - 4*(x**3) + 6*(x**2) - 4*x + 1     ≡   (x - 1)**4
// x**4 + 7*(x**3) + 18*(x**2) + 20*x + 8   ≡   (x + 1)(x + 2)**3
// x**2 + 2*x + 1                           ≡   (x + 1)**2
// --------------------------------

// =========
//  IL FAUT REORGANISER LE PROJET
//  EN PARTICULIER CREER DE .FSI CAR ON A BESOIN DES MATRICE PARTOUT (par exemple)
//  IL FAUT AUSSI FAIRE ATTENTION AVEC L'EGALITE DANS SUMPOW !! ELLE EST PUREMENT SYNTAXIQUE.
//  AUSSI, IL FAUT CREER UN MODULE POUR LES EQUATIONS.
// =========


// -------------------------------
// Le simplificateur boucle sur ça (SimpPureConst...) :
// let z = Polynomial.Interpolation.newtonUnivariatePolynomialInterpolation [| (SumPow.Const 1, SumPow.Const 2); (SumPow.Const 2, SumPow.Const 3); (SumPow.Const 3, SumPow.Const 5) |] (Name "x")
// let s, _ = Simplification.expandAndSimplify z |> Polynomial.Pattern.asUnivariatePolynomial (Name "x") []
// printfn "%s" (toLatexValue s)
// -------------------------------


// Faire un truc "Contract" / "Require" qui dit selon quelles conditions une expression / équation est valide





// 3*(x**4) - 8*(x**3) - 5*(x**2) + 16*x - 5
// 

//      let p = (inner [ "x**6 - 16" ]).[0]
//      let r = Polynomial.Factorization.IntegerCoefficients.RationalRoots.tryFactoring p
//      if r.IsSome then
//          printfn "%s = %s" (toLatexValue p) (List.fold (fun acc (a, deg) -> acc + sprintf @"\left(%s\right)^%d" (toLatexValue a) deg) "" r.Value)

//let a = (sp' >> toSumPow) "1/x"
//let points = NumericEvaluation.generatePoints2D -5. 5. 0.1 a "x" |> Array.map (function Constant x, Constant y -> x, y)
//Chart.Line points
//    |> Chart.withTitle (sprintf @"$%s$" (toLatex a).Value)
//    |> Chart.withMathTex (AppendTags = true)
//    |> Chart.show
//
//printfn "%A" points

// Il faut gérer ce qu'il se passe quand on a un 1/x par exemple

// while true do
//     printf " :  "
//     let inp = Console.ReadLine()
//     let a' = (toSumPow << sp') inp
//     let s' = Simplification.simplify a'
//     printfn "%s = %s\n" (toLatexValue a') (toLatexValue s')


// let variables = [
//     newVariable "a" KindInteger 1 10
//     newVariable "b" KindInteger 1 4
//     newVariable "c" KindInteger 1 3
//     newVariable "d" KindInteger 2 8
//     newVariable "e" KindInteger 3 6
//     newVariable "f" KindInteger 3 10
//     newVariable "g" KindInteger 4 8
//     newVariable "h" KindInteger 4 7
//     newVariable "i" KindInteger 5 6 ]

// let rnd = Random()
// 
// let foo = function
//     | 0 -> KindInteger
//     | 1 -> KindFloat
//     | 2 -> KindString
//     | 3 -> KindSymbol
// 
// let n = 15
// let variables =
//     [| for i = 0 to n do
//         let s = rnd.Next(i, n)
//         newVariable (sprintf "%c" (char (65 + i))) (foo <| rnd.Next(0, 4)) s (rnd.Next(s + 1, n*2)) |]
// 
// let t = linearScan variables 3
// prettyPrintVariable t

// SYMBOLIC PATTERN MATCHING
//  - https://www.numbas.org.uk/behind-the-design/pattern-matching.html
//  - https://www.academia.edu/16544453/Symbolic_Pattern_Matching_in_Clojure
//  - https://robowiki.net/wiki/Symbolic_Pattern_Matching
//  - https://www.google.be/search?q=symbolic+pattern+matching&newwindow=1&sxsrf=ALiCzsZa9qagKkSvmfZPc7fAougBkzyW7Q%3A1659791815338&source=hp&ei=x2nuYrukEZTzsAeEzJ-QCg&iflsig=AJiK0e8AAAAAYu531yiknqTJ7ttGvqj8F_NIItg3LfVz&oq=symbolic+pattern+mat&gs_lcp=Cgdnd3Mtd2l6EAMYADIGCAAQHhAWMgUIABCGAzIFCAAQhgMyBQgAEIYDOgQIIxAnOgQIABBDOggIABCABBCxAzoGCAAQHhAKOgIIJjoFCAAQgAQ6CwgAEIAEELEDEIMBOgoIABCABBCHAhAUOgoIABAeEA8QFhAKUABY1Slg3DFoAXAAeACAAaoBiAGGC5IBBDE0LjKYAQCgAQE&sclient=gws-wiz
//  - https://en.wikipedia.org/wiki/Denotational_semantics


// Fasm.NET ne marche pas, mais en vrai osef un peu, ceci par contre est important :
//  - https://github.com/lolp1/Process.NET : pour injecter et exécuter du code
//  - https://esozbek.me/blog/inline-assembly-in-csharp-and-dotnet/ : exemple de comment ça s'utilise
//  - https://github.com/icedland/iced : pour encoder des instructions




//open Liyh.Kernel.Atomic
//open Liyh.Kernel.Transform
//
////let rule1 = ("Add[?a, 0]" |-> "?a") "neutral-elem"
////let rule2 = ("Div[0, ?b]" ?-> "0") "NotEqual[?b, 0]" null
////printfn "%s" (string rule2)
//
//let test =
//    { RuleClass.name = "Test"
//      RuleClass.rules =
//        [ ("Add[?a, 0]" |-> "?a") null
//          ("Add[1, 2]" |-> "3") null
//          ("Add[?a, ?b]" |-> "Add[?b, ?a]") null ] }
//
//let r = reduce test !< "Add[4, Add[2, 0]]"

// https://nvie.com/posts/a-successful-git-branching-model/

