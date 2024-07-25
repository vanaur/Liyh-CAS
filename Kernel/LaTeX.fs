namespace Liyh.Kernel

[<RequireQualifiedAccess>]
module Latex =
    open System.Text

    type public DocumentType =
        | Article
        | Snippet
        | Other of documentClass: string

    type public Latex (documentType: DocumentType) =
        let result = StringBuilder()

        new() = Latex Snippet

