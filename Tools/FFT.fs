namespace Liyh.Utils

module FFT =
    open System.Numerics

    let private fac k n =
        let m2pi = -4. * acos 0.
        Complex.FromPolarCoordinates(1., m2pi * float k / float n)

    let private merge l r n =
        let f (k, t) x = (k + 1, (fac k n) * x :: t)
        let z = List.rev (snd (List.fold f (0, []) r))
        List.map2 ( + ) l z @ List.map2 ( - ) l z

    /// Recursive Cooley–Tukey fast Fourier transform.
    let public fft lst =
        let rec ditfft2 a n s =
            if n = 1 then
                [ List.item a lst ]
            else
                let odd = ditfft2 a (n / 2) (2 * s)
                let even = ditfft2 (a + s) (n / 2) (2 * s)
                merge odd even n

        ditfft2 0 (List.length lst) 1
