namespace Liyh.Language.Evaluation

// https://codingvision.net/c-load-dll-at-runtime

module Foreign = // du coup faire un FFI DOTNET & C
    open System.Reflection
    open System

    (* Liyh currently provides an interface for .NET's Foreign Function Interface (FFI), allowing anything
       written in languages like C#, F# that runs on .NET to theoretically be usable from Liyh. *)

    exception public LibNotFoundException of libPath: string
    exception public FunctionNotFoundException of libPath: string * className: string * fname: string

    /// Defines a foreign function interface for a given dotnet library.
    type public FFI (libPath: string) =
        let assembly =
            if IO.File.Exists libPath then Assembly.LoadFrom libPath
            else raise (LibNotFoundException libPath)

        /// Checks whether the given class exists.
        member public __.ExistsClass className =
            match assembly.GetType className with
            | null -> false
            | _ -> true

        /// Returns an array of all the methods of a given class.
        member public __.GetMethods className =
            let ty = assembly.GetType className
            ty.GetMethods ()

        /// Calls a function of the given class and with the arguments supplied.
        member public this.Call className fname args =
            let methods = this.GetMethods className

            match Array.tryFind (fun (method: MethodInfo) -> method.Name = fname) methods with
            | None -> raise (FunctionNotFoundException (libPath, className, fname))
            | Some method ->
                let ty = assembly.GetType className
                let inst = Activator.CreateInstance ty
                
                method.Invoke(inst, args)
