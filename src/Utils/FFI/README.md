# Liyh's dynamic FFI mini library

This mini library features a dynamic [foreign function interface](https://en.wikipedia.org/wiki/Foreign_function_interface) targeting C, i.e. dynamic libraries written in C can be loaded and their contents used at runtime without prior compile-time information in the F# program. Of course, it's designed to be used as the FFI of an interpreter for a programming language written in F# (or any dotnet language).

This mini-library is experimental for the moment and does not yet handle advanced data types (such as structures and unions or advanced pointer manipulation), but normally already allows you to

 - Load dynamic libraries (`.so` or `.dll` depending on platform) ;
 - Invoke functions exposed therein ;

The following C types are normally supported: `int32`, `int64`, `float`, `double`, `single`, `char`, `string` (i.e `char*`), pointers of any depth (e.g `double**`) and `void` in both directions (F# ⟷ C).

## Performance
We haven't carried out any real performance tests for now, but there's no need to do so to warn potential users that using such an FFI isn't free in terms of performance. The library must use reflection to function, which comes at a cost: each function that is invoked has a `delegate` built dynamically, but once this `delegate` has been built, future calls to the function won't cost any more `delegate` construction.

## Use cases
In the case of Liyh, only the following use cases will justify the use of an FFI (in "official" development):

 - Use features that *cannot* be implemented in the language or provided by the compiler (e.g. `libcurl` or some UI);
 - Nothing else, usually.

## Examples
Examples are better than long explanations, and the code is normally not too difficult for a user to follow. For the rest of the examples, we will consider the following C toy library:

<details>
  <summary>LibTest.c</summary>

```c
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

// Example of function that take simple integers and return another integer.
int addition(int a, int b)
{
    return a + b;
}

// Example of function that take simple doubles and return another double.
double multiply_doubles(double a, double b)
{
    return a * b;
}

// Example of function that take no argument and return a character string.
char* get_greeting()
{
    char* greeting = malloc(14);
    strcpy(greeting, "Hello, World!");

    return greeting;
}

// Example of function that take two character strings and return another character string.
char *concatenate(const char *str1, const char *str2)
{
    size_t len1 = strlen(str1);
    size_t len2 = strlen(str2);

    char *result = malloc(len1 + len2 + 1);

    strcpy(result, str1);
    strcat(result, str2);

    return result;
}

// Example of a function that take an array and return a double.
double sumArray(double* array, int len)
{
    double result = 0;

    for (int i = 0; i < len; i++)
        result += array[i];

    return result;
}

// Example of a function that take a character string and return an array.
int* asciiCharacters(char* str)
{
    int len = strlen(str);
    int* result = malloc(len * sizeof(char));

    for (int i = 0; i < len; i++)
        result[i] = (int)str[i];

    return result;
}

// Example of a function that return an array of strings.
char** greetings()
{
    char** result = malloc(3 * sizeof(char*));

    result[0] = malloc(sizeof("hello"));
    result[1] = malloc(sizeof("bonjour"));
    result[2] = malloc(sizeof("hola"));

    strcpy(result[0], "hello");
    strcpy(result[1], "bonjour");
    strcpy(result[2], "hola ");

    return result;
}

// Example of a function that update a pointer.
void updateByOne(int* value)
{
    (*value)++;
}

// Example of a function that take two arrays and return another array. 
double* vecAdd(double* vec1, double* vec2, int len)
{
    double* result = malloc(len * sizeof(double));

    for (int i = 0; i < len; i++)
        result[i] = vec1[i] + vec2[i];

    return result;
}

```

</details>
We then have the following examples.

### `int addition(int a, int b)`

```fs
open Liyh.FFI.CFFI

let lib = DynLib.Load "./libtestlib.so"

let signature =
    { returnType = CType.Int32
      parameters = [| CType.Int32; CType.Int32 |] }

let result = lib.InvokeFunction "addition" signature [| 21 :> obj; 18 :> obj |] :?> int32
```

### `double multiply_doubles(double a, double b)`

```fs
open Liyh.FFI.CFFI

let lib = DynLib.Load "./libtestlib.so"

let signature =
    { returnType = CType.Double
      parameters = [| CType.Double; CType.Double |] }

let result = lib.InvokeFunction "multiply_doubles" signature [| 3.0 :> obj; 7.0 :> obj |] :?> double
```

### `char* get_greeting()`

```fs
let lib = DynLib.Load "./libtestlib.so"

let signature =
    { returnType = CType.Pointer CType.String
      parameters = [| |] }

let ptr = lib.InvokeFunction "get_greeting" signature [| |] :?> nativeint
let stringResult = Marshal.PtrToStringAnsi ptr
```

### `char *concatenate(const char *str1, const char *str2)`

```fs
let lib = DynLib.Load "./libtestlib.so"

let signature =
    { returnType = CType.Pointer CType.String
      parameters = [| CType.String; CType.String |] }

let ptr = lib.InvokeFunction "concatenate" signature [| "Hello, " :> obj; "world!" :> obj |] :?> nativeint
let stringResult = Marshal.PtrToStringAnsi ptr
```

### `double sumArray(double* array, int len)`

```fs
let lib = DynLib.Load "./libtestlib.so"

let signature =
    { returnType = CType.Double
      parameters = [| CType.Pointer CType.Double; CType.Int32 |] }

let data: double[] = [| 0.0 .. 100.0 |]
let dataPtr = Marshal.AllocHGlobal(data.Length * sizeof<double>)
Marshal.Copy(data, 0, dataPtr, data.Length)

let result = lib.InvokeFunction "sumArray" signature [| dataPtr :> obj; data.Length :> obj |] :?> double

// Free the allocated memory
Marshal.FreeHGlobal dataPtr
```

### `int* asciiCharacters(char* str)`

```fs
let lib = DynLib.Load "./libtestlib.so"

let signature =
    { returnType = CType.Pointer CType.Int32
      parameters = [| CType.String |] }

let arg = "abcdefg"
let ptr = lib.InvokeFunction "asciiCharacters" signature [| arg :> obj |] :?> nativeint

let result = Array.zeroCreate<int32>(arg.Length)
Marshal.Copy(ptr, result, 0, arg.Length)

// Free the allocated memory
Marshal.FreeHGlobal ptr
```

### `char** greetings()`

```fs
let lib = DynLib.Load "./libtestlib.so"

let signature =
    { returnType = CType.Pointer CType.String
      parameters = [| |] }

let ptr = lib.InvokeFunction "greetings" signature1 [| |] :?> nativeint
let result = Array.zeroCreate<nativeint>(3) // We know that the function return a 3-array.
Marshal.Copy(ptr, result1, 0, 3)

let arrayResult = Array.map Marshal.PtrToStringAnsi result1

// Free the allocated memory
Marshal.FreeHGlobal ptr
```

### `void updateByOne(int* value)`

```fs
let lib = DynLib.Load "./libtestlib.so"

let signature =
    { returnType = CType.Void
      parameters = [| CType.Pointer CType.Int32 |] }

let mutable myValue = 8
let ptr = NativePtr.toNativeInt<int32> &&myValue
let _ = lib.InvokeFunction "updateByOne" signature [| ptr :> obj |]

// `myValue` is now equals to 9.
```

### `double* vecAdd(double* vec1, double* vec2, int len)`

```fs
let lib = DynLib.Load "./libtestlib.so"

let signature =
    { returnType = CType.Pointer CType.Double
      parameters = [| CType.Pointer CType.Double; CType.Pointer CType.Double; CType.Int32 |] }

let rnd = Random()
let n = 700

let mutable vec1 = [| for _ in 0 .. n -> rnd.NextDouble() |]
let mutable vec2 = [| for _ in 0 .. n -> rnd.NextDouble() |]

let vec1Ptr = Marshal.AllocHGlobal(vec1.Length * sizeof<double>)
let vec2Ptr = Marshal.AllocHGlobal(vec2.Length * sizeof<double>)

Marshal.Copy(vec1, 0, vec1Ptr, vec1.Length)
Marshal.Copy(vec2, 0, vec2Ptr, vec1.Length)

let vecResPtr = lib.InvokeFunction "vecAdd" signature [| vec1Ptr :> obj; vec2Ptr :> obj; vec1.Length :> obj |] :?> nativeint

// // Free the allocated memory
Marshal.FreeHGlobal vec1Ptr
Marshal.FreeHGlobal vec2Ptr
Marshal.FreeHGlobal vecResPtr
```

---

