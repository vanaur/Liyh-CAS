use Liyh.Statistics

data := Read['data.dat', format: FileFormat.GnuPlot]

set m, p : Real
f[x] := Regression[x -> m*x+p, xdata: data.[0], ydata: data.[1]]

perform Plot[data] + Plot[f]
