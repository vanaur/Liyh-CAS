namespace Liyh.Kernel.Plotting

module UI =
    open System
    open Eto.Drawing
    open Eto.Forms

    type private LiyhPlottingUI(path: string) as this =
        inherit Form()

        do
            this.Title      <- "Liyh"
            this.ClientSize <- Size (800, 700)
            this.Content    <- new WebView(Url = new Uri(path))

    let public display imagePath =
        let app = new Application()
        let form = new LiyhPlottingUI(imagePath)

        form.Show()
        app.Run()


(*
open ScottPlot
open ScottPlot.Eto
open Eto.Drawing
open Eto.Forms

type LiyhGUI() as this =
    inherit Form()

    let plotView = new PlotView()
    let fn1 = new Func<float, float Nullable>(fun x -> Math.Log x)

    do
        plotView.Plot.AddFunction(fn1) |> ignore
        plotView.Plot.Style(Style.Burgundy)
        plotView.Plot.Palette <- Palette.Frost
        plotView.Plot.XLabel("x")
        plotView.Plot.YLabel("y")

        this.Title      <- "Liyh"
        this.ClientSize <- Size (800, 700)
        this.Content    <- plotView

let app = new Application()
let form = new LiyhGUI()

form.Show()
app.Run()
*)
