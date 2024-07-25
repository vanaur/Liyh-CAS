namespace Liyh.Kernel.Builtin

module Plot =
    open Liyh.Kernel.Plotting
    open Liyh.Kernel.SumProd
    open System.Linq

//    let public plot (parameters: SumProd list) =
//        let title =
//            match parameters.Head with
//            | Other (String (str)) -> str
//            | other -> failwithf "Not a string: `%s`" other.ToLatex
//
//        let is2tuple =
//            function
//            | Other (Tuple [ Float _; Float _ ]) -> true
//            | Other (Tuple [ Number _; Number _ ]) -> true
//            | Other (Tuple [ Number _; Float _ ]) -> true
//            | Other (Tuple [ Float _; Number _ ]) -> true
//            | _ -> false
//
//        let get2tuple =
//            function
//            | Other (Tuple [ Float x; Float y ]) -> (x, y)
//            | Other (Tuple [ Number x; Number y ]) -> (float x, float y)
//            | Other (Tuple [ Number x; Float y ]) -> (float x, y)
//            | Other (Tuple [ Float x; Number y ]) -> (x, float y)
//            | _ -> failwith "Not a 2-tuple."
//
//        match parameters.Tail with
//        | Other (Vector (xs)) :: [] when xs.All is2tuple ->
//            let xs = List.map get2tuple xs
//            let r = LiyhPlot2D.LiyhChart2DType.ChartPoint xs
//            LiyhPlot2D.LiyhPlot2D((r, title))
//
//        | other -> failwithf "Unhandled yet, %A" other
