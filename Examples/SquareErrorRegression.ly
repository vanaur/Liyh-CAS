use Liyh.Statistics

xdata, ydata := Read['data.dat', format: FileFormat.GnuPlot]

xerror := Map[x => Sqrt[x], xdata]
yerror := Map[y => Sqrt[y], ydata]

set A, lambda : Real

f[t] := Regression[t => A * Exp[-lambda * t], xdata: xdata, ydata: ydata, xerror: xerror, yerror: yerror]

perform Plot[f] + Plot[xdata, ydata]

