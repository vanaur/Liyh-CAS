namespace Liyh.Internal

module DiagnosticKinds =
    open FParsec

    /// An element is located as an initial and final position.
    type public Location = Position * Position

    /// Differents types of possible diagnostics.
    type public DiagnosticKind =
        | DiagnosticError of string
        | DiagnosticWarning of string
        | DiagnosticNote of string
        | DiagnosticInternal of string

    /// Indicates the importance of a diagnostic, how useful it is and therefore defines
    /// the verbosity of the compiler.
    type public DiagnosticImportance =
        /// Very important.
        | Major

        /// Always displayed, regardless of importance (especially for internal errors).
        | Always

        /// Fairly important.
        | Important
        
        /// Not very important.
        | Unhelpful

    /// The different elements characterising a diagnosis.
    type public DiagnosticInfo =
        {
          /// Defines whether the diagnostic object is internal (not related to the user) or not.
          isInternal: bool

          /// The type of information that the diagnostic sends.
          kind: DiagnosticKind

          /// The relevant syntactic element to be displayed, if it exists.
          relevantElement: string option

          /// Location of the item of interest to be displayed.
          location: Location option

          /// To which stream the object of the diagnosis is from.
          streamName: string option

          /// Messages to be displayed.
          messages: string list

          importance: DiagnosticImportance

          /// The code/type of the message, if any.
          code: uint option }

    type public Verbosity =
        | Level1 = 1   // Display all information (default)
        | Level2 = 2   // Display all information except `Unhelpful`, `begin ()` and `conclude ()`
        | Level3 = 3   // Only display `Important` and `Major`
        | Level4 = 4   // Only display `Major`

