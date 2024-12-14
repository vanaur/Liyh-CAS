namespace Liyh.Kernel

module public LiyhPlotStyle =
    open Plotly.NET
    open Plotly.NET.LayoutObjects

    let private minimalStyle =
        let fontStyle =
            Font.init (
                Family = StyleParam.FontFamily.Custom "Inter, Arial, sans-serif",
                Size = 12.,
                Color = Color.fromHex "#333333"
            )

        let axisStyle =
            LinearAxis.init (
                GridColor = Color.fromHex "#e0e0e0",
                ZeroLineColor = Color.fromHex "#999999",
                ZeroLineWidth = 2.,
                LineWidth = 2.,
                TickColor = Color.fromHex "#666666",
                LineColor = Color.fromHex "#666666",
                NTicks = 10,
                ShowLine = true,
                ShowGrid = true,
                Mirror = StyleParam.Mirror.True
            )

        let plotConfig =
            Config.init (
                Responsive = true,
                StaticPlot = true
            )

        let layoutStyle =
            Layout.init (
                Font = fontStyle,
                PaperBGColor = Color.fromString "transparent",
                PlotBGColor = Color.fromString "transparent",
                Margin = Margin.init (Left = 50., Right = 50., Top = 50., Bottom = 50.)
            )

        let sceneStyle =
            Scene.init (
                XAxis = axisStyle,
                YAxis = axisStyle,
                ZAxis = axisStyle,
                AspectMode = StyleParam.AspectMode.Cube,
                BGColor = Color.fromString "white"
            )

        {| Layout = layoutStyle
           Config = plotConfig
           Axis = axisStyle
           Scene = sceneStyle |}

    let public createMinimalChart data =
        let style = minimalStyle

        Chart.combine data
        |> Chart.withLayout style.Layout
        |> Chart.withConfig style.Config
        |> Chart.withXAxis style.Axis
        |> Chart.withYAxis style.Axis
        |> Chart.withZAxis style.Axis
        |> Chart.withScene style.Scene
        |> Chart.withMathTex true
        |> Chart.withLegend false

module public Plot =
    open Plotly.NET
    open Plotly.NET.ImageExport

