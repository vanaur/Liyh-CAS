namespace Liyh.Kernel.Plotting

module LiyhPlot2D =
    open Liyh.Kernel.Plotting
    open Plotly.NET.ImageExport
    open Plotly.NET

    type public LiyhChart2DType =
        // Defines a point cloud.
        | ChartPoint of (float * float) list

        // Defines a point cloud and links them together with a rigid line.
        | ChartLine of (float * float) list

        // Defines a point cloud and links them together with a smooth line.
        | ChartSpline of (float * float) list

        // Defines the graph of a function.
        | ChartGraph of min: float * max: float * (float -> float)

    type public LiyhChart = LiyhChart2DType * string

    let private staticConfig = Config.init (StaticPlot = true)

    do Defaults.DefaultTemplate <- ChartTemplates.lightMirrored
    do Defaults.DefaultConfig <- staticConfig

    let private setChart (chartType, name) =
        match chartType with
        | ChartPoint xs -> Chart.Point(xs, Name = name)
        | ChartLine xs -> Chart.Line(xs, Name = name)
        | ChartSpline xs -> Chart.Spline(xs, Name = name)
        | ChartGraph (min, max, fn) -> Chart.Line([ for x in min .. 0.01 .. max -> x, fn x ], Name = name)

    type public LiyhPlot2D(chartTypeList: LiyhChart list, gcharts: GenericChart.GenericChart list) =

        /// The final chart to be plotted.
        let mutable chart = Chart.Invisible()

        do
            chart <-
                List.map setChart chartTypeList @ gcharts
                |> Chart.combine
                |> Chart.withMathTex true

        new(chartType: LiyhChart) = LiyhPlot2D([ chartType ], [])
        new(chartTypeList: LiyhChart list) = LiyhPlot2D(chartTypeList, [])
        new(gcharts: GenericChart.GenericChart list) = LiyhPlot2D([], gcharts)
        new(gchart: GenericChart.GenericChart) = LiyhPlot2D([], [ gchart ])

        /// Return the generic chart.
        member __.GetChart = chart

        /// Export the graph as JPG image to the given path.
        member __.ImageExport path = Chart.saveJPG path chart

        /// Display a window with the interactive plot.
        member __.Display () =
            let path = System.AppDomain.CurrentDomain.BaseDirectory + ((hash >> string) chart)
            Chart.saveHtml path chart
            UI.display (path + ".html")
            System.IO.File.Delete (path + ".html")

        /// Give a title to the plot.
        member __.SetTitle title =
            chart <- Chart.withTitle (Title.init title) chart

        /// ditto.
        member __.SetXError (xErrorList: float list) =
            chart <- Chart.withXErrorStyle (Array = xErrorList, Symmetric = true) chart

        /// ditto.
        member __.SetYError (yErrorList: float list) =
            chart <- Chart.withYErrorStyle (Array = yErrorList, Symmetric = true) chart

        /// Combine two LiyhPlot2D.
        static member ( + ) (plot1: LiyhPlot2D, plot2: LiyhPlot2D) =
            new LiyhPlot2D([plot1.GetChart; plot2.GetChart])

