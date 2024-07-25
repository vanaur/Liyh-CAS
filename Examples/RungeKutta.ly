use Liyh.Types

||| Finds a value of `y` for a given `x` using step size `h` and initial value `y0` at `x0`.
procedure RungeKutta[x0: Real, y0: Real, x: Real, h: Real or 0.5, fn: Real -> Real]
   n := (x - x0) / h :: Integer

   mutable y := y0
   mutable x0 := x0

   for i in Range[1, n + 1]

      k1 := h * f[x0, y]
      k2 := h * f[x0 + 0.5 * h, y + 0.5 * k1]
      k3 := h * f[x0 + 0.5 * h, y + 0.5 * k2]
      k4 := h * f[x0 + 1.0 * h, y + 1.0 * k3]

      y <- y + (k1 + 2 * k2 + 2 * k3 + k4) / 6
      x0 <- x0 + h

   return y

t := RungeKutta[x0: 0, y0: 1, x: 2, fn: (x y -> (x - y) / 2)]

