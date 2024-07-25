namespace Liyh.Language.Syntax

module Location =
    open FParsec

    ///An element is located as an initial and final position.
    type public Location = Position * Position

    /// An `OpName` corresponds to an identifier that is located.
    type public OpName = string * Location
