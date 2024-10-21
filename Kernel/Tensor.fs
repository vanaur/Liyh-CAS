namespace Liyh.Kernel

#nowarn "3391"
#nowarn "25"
#nowarn "46"

/// This module deals with classical tensor algebra over SumPow and index notation.
module public rec Tensor =
    open Liyh.Kernel.Index
    open Liyh.Utils
    open Liyh.Kernel
    open Liyh.Kernel.LinearAlgebra
