namespace Liyh.FFI

/// Loads useful functions for Windows.
module private Kernel32 =
    open System.Runtime.InteropServices

    [<DllImport("kernel32", SetLastError = true)>]
    extern nativeint LoadLibrary(string path)
    
    [<DllImport("kernel32", SetLastError = true)>]
    extern nativeint GetProcAddress(nativeint handle, string procName)
    
    [<DllImport("kernel32", SetLastError = true)>]
    extern bool FreeLibrary(nativeint handle)

/// Loads useful functions for Linux.
module private LibDl =
    open System.Runtime.InteropServices

    [<DllImport("libdl")>]
    extern nativeint dlopen(string path, int flags)
    
    [<DllImport("libdl")>]
    extern nativeint dlsym(nativeint handle, string symbol)
    
    [<DllImport("libdl")>]
    extern nativeint dlerror()
    
    [<DllImport("libdl")>]
    extern int dlclose(nativeint handle)
    
    let RTLD_NOW = 2

module private DelegateBuilder =
    open System
    open System.Reflection
    open System.Reflection.Emit

    let private assemblyBuilder =
        AssemblyBuilder.DefineDynamicAssembly(AssemblyName("DynamicDelegates"), AssemblyBuilderAccess.Run)

    let private moduleBuilder =
        assemblyBuilder.DefineDynamicModule("DynamicDelegateModule")

    let public BuildDelegateType (parameterTypes: Type[], returnType: Type) =
        let typeBuilder =
            moduleBuilder.DefineType(
                sprintf "DynamicDelegate_%d" (Guid.NewGuid().GetHashCode()),
                TypeAttributes.Class
                ||| TypeAttributes.Public
                ||| TypeAttributes.Sealed
                ||| TypeAttributes.AnsiClass
                ||| TypeAttributes.AutoClass,
                typeof<MulticastDelegate>
            )

        let ctor =
            typeBuilder.DefineConstructor(
                MethodAttributes.RTSpecialName
                ||| MethodAttributes.HideBySig
                ||| MethodAttributes.Public,
                CallingConventions.Standard,
                [| typeof<obj>; typeof<IntPtr> |]
            )

        ctor.SetImplementationFlags(MethodImplAttributes.Runtime ||| MethodImplAttributes.Managed)

        let invokeMethod =
            typeBuilder.DefineMethod(
                "Invoke",
                MethodAttributes.Public
                ||| MethodAttributes.HideBySig
                ||| MethodAttributes.NewSlot
                ||| MethodAttributes.Virtual,
                returnType,
                parameterTypes
            )

        invokeMethod.SetImplementationFlags(MethodImplAttributes.Runtime ||| MethodImplAttributes.Managed)

        typeBuilder.CreateType()

/// This module features a dynamic foreign function interface targeting C, i.e. dynamic libraries written in C can be
/// loaded and their contents used at runtime without prior compile-time information. This mini-library is experimental
/// for the moment and does not yet handle advanced data types (such as structures, unions or advanced arrays).
module public CFFI =
    open System
    open System.IO
    open System.Runtime.InteropServices
    open System.Collections.Concurrent

    exception public UnknownErrorLoadingLibraryException of path: string
    exception public ErrorLoadingLibraryException of path: string * msg: string
    exception public FunctionNotFoundException of libName: string * fname: string * msg: string
    exception public IncorrectNumberOfArgumentsException of libName: string * fname: string * expect: int * given: int

    /// Pattern-match a native pointer.
    let inline private (|ZeroIntPtr|_|) (n: nativeint) =
        if n = 0n then Some () else None

    [<Struct; RequireQualifiedAccess>]
    type public CType =
        | Int32     // int32
        | Int64     // int64
        | Char      // char
        | Float     // float
        | Double    // double
        | String    // char*
        | Pointer   // int*
        | Void      // void

    [<Struct>]
    type public FunctionSignature =
        { returnType: CType
          parameters: CType[] }

    let inline private convertIntPtrToStringObj (value: obj) =
        match value :?> nativeint with
        | ZeroIntPtr -> null
        | ptr ->
            let str = Marshal.PtrToStringAnsi ptr
            Marshal.FreeHGlobal ptr
            str :> obj

    let private cTypeToParamType =
        function
        | CType.Int32 -> typeof<int32>
        | CType.Int64 -> typeof<int64>
        | CType.Char -> typeof<char>
        | CType.Float -> typeof<float32>
        | CType.Double -> typeof<double>
        | CType.String -> typeof<string>
        | CType.Pointer -> typeof<nativeint>
        | CType.Void -> typeof<Void>

    let private cTypeToReturnType =
        function // The conversion from CType to Type is the same except for arrays / strings for the value return!
        | CType.String -> typeof<nativeint>
        | ctype -> cTypeToParamType ctype

    /// Creates an instance of the given dynamic library, allowing its contents to be dynamically loaded and called.
    /// 
    /// Usage example:
    /// 
    ///     let lib = DynamicLibrary.Load("/.../myLibrary")
    /// 
    ///     let myFunctionSignature = {
    ///         returnType = CType.Int32
    ///         parameters: [| CType.Int32; CType.Int32 |]
    ///     }
    /// 
    ///     let myFunctionResult =
    ///         lib.InvokeFunction "myFunctionName" myFunctionSignature [| 5 :> obj; 3 :> obj |] :?> int
    /// 
    /// In this example, we assume a function of the form `f: (int, int) -> int`, call it and convert its return type to int.
    type public DynLib private (handle: nativeint, libName: string) =
        let mutable disposed = false

        /// A cache for the generated dynamic methods. The key is the function's name and signature, and the
        /// associated value is the created delegate. We use a concurrent dictionary for thread safety.
        let methodCache = ConcurrentDictionary<string * FunctionSignature, Delegate>()

        /// Loads the given library, throws an exception on error.
        static member public Load (path: string) =
            let libName = Path.GetFileNameWithoutExtension path

            if not (File.Exists path) then
                raise (FileNotFoundException(sprintf "The library '%s' has not been found." libName, path))

            if RuntimeInformation.IsOSPlatform OSPlatform.Linux then
                LibDl.dlerror () |> ignore

                match LibDl.dlopen(path, LibDl.RTLD_NOW) with
                | ZeroIntPtr ->
                    match LibDl.dlerror() with
                    | ZeroIntPtr -> raise (UnknownErrorLoadingLibraryException path)
                    | error -> raise (ErrorLoadingLibraryException (path, Marshal.PtrToStringAnsi error))

                | handle -> new DynLib(handle, libName)

            else
                match Kernel32.LoadLibrary path with
                | ZeroIntPtr -> raise (ErrorLoadingLibraryException (path, Marshal.GetLastWin32Error() |> string))
                | handle -> new DynLib(handle, libName)

        member private this.CreateDynamicDelegate (signature: FunctionSignature) =
            let parameterTypes = Array.map cTypeToParamType signature.parameters
            let returnType = cTypeToReturnType signature.returnType

            DelegateBuilder.BuildDelegateType(parameterTypes, returnType)

        /// Invokes the function specified by its name and signature, and supplies the given arguments.
        /// Throws an exception if the function is not correctly invoked.
        member public this.InvokeFunction (fname: string) (signature: FunctionSignature) (args: obj[]) =
            if disposed then invalidOp "The library has been disposed"

            if Array.length args <> Array.length signature.parameters then
                raise (IncorrectNumberOfArgumentsException
                            (libName, fname, Array.length signature.parameters, Array.length args))

            let procAddr =
                if RuntimeInformation.IsOSPlatform OSPlatform.Windows
                then Kernel32.GetProcAddress(handle, fname)
                else LibDl.dlsym(handle, fname)

            if procAddr = 0n then
                let error = 
                    if RuntimeInformation.IsOSPlatform OSPlatform.Windows
                    then Marshal.GetLastWin32Error() |> string
                    else LibDl.dlerror() |> Marshal.PtrToStringAnsi

                raise (FunctionNotFoundException (libName, fname, error))

            // -- Use or create a new delegate for the given function -- //

            let key = (fname, signature)
            let delegate' =
                match methodCache.TryGetValue key with
                | true, delegate' -> delegate'
                | _ ->
                    let delegateType = this.CreateDynamicDelegate signature
                    let newDelegate = Marshal.GetDelegateForFunctionPointer(procAddr, delegateType)
                    methodCache.GetOrAdd(key, newDelegate)

            try
                let result = delegate'.DynamicInvoke args

                if signature.returnType = CType.String
                then convertIntPtrToStringObj result
                else result

            finally

                // -- Frees up memory if needed -- //

                Array.zip signature.parameters args
                |> Array.iter (function
                    | CType.String, (:? nativeint as ptr) -> if ptr <> 0n then Marshal.FreeHGlobal ptr
                    | _ -> ())

        interface IDisposable with

            member this.Dispose() =
                if not disposed then
                    if RuntimeInformation.IsOSPlatform OSPlatform.Windows
                    then Kernel32.FreeLibrary handle |> ignore
                    else LibDl.dlclose handle |> ignore

                    disposed <- true

    // -- Object conversion helpers -- //

    let inline public convertObjToInt32 (value: obj) = value :?> int32
    let inline public convertObjToInt64 (value: obj) = value :?> int64
    let inline public convertObjToFloat (value: obj) = value :?> float
    let inline public convertObjToDouble (value: obj) = value :?> double
    let inline public convertObjToString (value: obj) = value :?> string
    let inline public convertObjToPointer (value: obj) = value :?> nativeint
    let inline public convertObjToVoid (value: obj) = value :?> unit

