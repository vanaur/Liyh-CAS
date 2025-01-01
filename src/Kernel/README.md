# Kernel
Liyh's little *symbolic algebra* kernel (~6K LoC).

The aim of the kernel is to provide the essential and general elements of *computer algebra*, including but not limited to:

 - **Constant** handling via
   - [`Constant.fs`](Constant.fs) – consists of representing an arbitrary integer or floating-point numerical constant.
   - [`RepeatingDecimalNumber.fs`](RepeatingDecimalNumber.fs) – consists of representing a number whose decimal places repeat infinitely.
   - [`Prime.fs`](Prime.fs) – consists of manipulating prime numbers.
 - The representation of any **symbolic**, general and **abstract quantity** via
   - [`Atomic.fs`](Atomic.fs) – represents any element as a non-interpreted function or constant.
 - Representing and manipulating **algebraic expressions** via
   - [`SumPow.fs`](SumPow.fs) – represents a general algebraic field.
 - Representing and manipulating **polynomial** expressions via
   - [`Polynomial.fs`](Polynomial.fs) – represents univariate and multivariate general polynomials whose coefficients are in SumPow.
 - Represent and manipulate **matrices**, **vectors** and **tensor** expressions via
   - [`MultiLinearAlgebra.fs`](MultiLinearAlgebra.fs) – represent and manipulate matrices, vectors and tensor expressions.
 - Represent and solve **equations** symbolically and numerically via
   - [`Equation.fs`](Equation.fs) – represents the different kinds of equation as well as numerical solvers.
   - [`Solve.fs`](Solve.fs) – contains methods for solving equations.
 - Implement algebraic and numerical methods for **calculus** problems via
   - [`Calculus.fs`](Calculus.fs) – implements algorithms for evaluating limits, derivatives, integrals and series.
 - Miscellaneous mathematical elements via
   - [`Tools.Utils.Math`](../Tools/Utils.fs) – implements some useful and general maths methods.
 - **Rendering** mathematical expressions via
   - [`MathRender.fs`](MathRender.fs) by design.
   - All symbolic objects are rendered with `MathRender` whenever possible.
 - Perform **numerical operations** via
   - [`Constant.fs`](Constant.fs) by nature.
   - [`SumPow.fs`](SumPow.fs) using `NumericEvaluation`.
   - [`Polynomial.fs`](Polynomial.fs) using `NumericEvaluation`.
   - [`MultiLinearAlgebra.fs`](MultiLinearAlgebra.fs) using `NumericEvaluation`.
   - [`Calculus.fs`](Calculus.fs) using `NumericEvaluation`.

## Current considerations

### Constant values
 - Liyh does not currently implement algebra on [arbitrary precision numbers](https://en.wikipedia.org/wiki/Arbitrary-precision_arithmetic) and implements most of arithmetic operation (on constants) via `double` (64 bits) and/or via `Complex` (2x 64 bits).

 - Internally, some temporary operations are performed using `bigint`, but the results are converted to `double`.

 - The authors are aware of the limitations in terms of double accuracy (according to IEEE). Precision is taken into account when comparing numerical values according to `Constant`. Equality is verified up to `e-14` accuracy. Beyond that point, the comparison is no longer considered valid.

Our choice was made for the following reasons:

 - It's rare to have to deal with numerical quantities with a precision greater than `15` to `17` significant decimal digits and an order of magnitude greater than `|e+307|`.

 - In the case of data that need to go beyond the numerical considerations mentioned above, we believe that a specialized rather than a generalist tool should be used instead.

 - We want good support for elementary functions, which is already a very difficult task in the case of the IEEE standard, but becomes even worse with arbitrary precision. Fortunately, the standard F# library implements a sufficient number of elementary functions that we can simply use.

 - Arbitrary precision numbers have a significant impact on performance.

 - This ensures compatibility with any numerical manipulation in F# or .NET.

 - At some point a choice had to be made, and this is the simplest one.

### Overall performance
 - Liyh's kernel isn't *highly* optimised and misses out on certain optimisations to improve readability, usability and ease. However, the algorithms used and their implementation are written well enough (a priori) not to result in poor performance.

 - The Liyh kernel, and in particular everything to do with [`SumPow.fs`](SumPow.fs) (including all the contents of the file), is highly mutually recursive, which can have an impact on performance.

 - Searching for fixed points in simplifications can slow down execution.

 - Parallelism is only used to generate large quantities of numerical data (in particular to generate graphs).

 - [Lazy evaluation](https://en.wikipedia.org/wiki/Lazy_evaluation) and [memoization](https://en.wikipedia.org/wiki/Memoization) are implemented notably in [`SumPow.fs`](SumPow.fs) to improve overall performance.

 - It is often very useful to use dictionaries (there are many of them in the code). F# provides the [`Map<'Key, 'Value>`](https://fsharp.github.io/fsharp-core-docs/reference/fsharp-collections-mapmodule.html) type which behaves like an immutable dictionary, but internally uses an AVL tree which does not always lend itself to the nature of the operations you perform with a dictionary. This sometimes has a significant impact on performance. A future version of Liyh could use another adapted structure to enhance performance.

 - Some specialised algorithms are implemented to provide better performance when the conditions are met.

### Rendering expressions
Liyh provides access to a small library presenting an intermediate abstract markup language specialized in rendering mathematical expressions, [`MathRender.fs`](MathRender.fs). The aim of this little lib is to provide an abstract representation for the layout of mathematical symbols and expressions, the final result of which can be compiled into a real markup language. Liyh currently *partially* supports

 - [LaTeX](https://www.latex-project.org/) (mathmode) – this is the default support, and probably the most useful.
 
 - [Typst](https://typst.app/) (mathmode) – this markup language is very promising and we want to target it.
 
 - [MathML](https://developer.mozilla.org/en-US/docs/Web/MathML) – currently poorly supported, and probably little effort to support it further. Who actually uses MathML these days? We support it mainly for the proof-of-concept.

Since rendering is unified, compilation into a real markup language is straightforward and, normally, uniform between the markup languages available (indeed, the structure of a `MathRender` object remains the same regardless of the target).

By definition, every symbolic object (`ISymbolic`) must implement a method returning a `MathRender` object (only if this makes sense, otherwise the method can return `None`). This means that any mathematical symbol present in the Liyh kernel can be mathematically rendered.

### Simplification vs. reduction
 - The simplifications consist of calculate algebraically (and therefore symbolically) the expressions that can be mutually or individually transformed into a simpler expression. For example `a + a = 2a`, `Sqrt[8] = 2*Sqrt[2]` or `16/12 = 8/6`.

 - Reductions include simplifications and add more sophisticated simplifications/rewritings, generally involving theorems or identities. For example, `Cos[a]² + Sin[a]² = 1`. Reductions also depend on a given context (a context is a set of equalities or inequalities that certain variables must respect).

### Equality
 - The equality of expressions is generally a difficult and sometimes undecidable problem. The kernel implements equality in a syntactic, albeit slightly more general, way.

 - Expressions that are equal but syntactically quite different are not currently handled well.

 - The `EqualityTest` module in [`SumPow.fs`](SumPow.fs) introduces an equality function that uses numerical and slightly statistical heuristics to check whether two expressions are equal. This is more efficient than an algebraic solution for large or complicated expressions, but is more likely to give the wrong answer, even if the implementation strives to provide the best possible result.

---

