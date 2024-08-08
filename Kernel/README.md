# Kernel
Liyh's little *symbolic algebra* kernel.

The aim of the kernel is to provide the essential and general elements of computer algebra, including:

 - Constant handling via
   - [`Constant.fs`](Constant.fs) – consists of representing an arbitrary integer or floating-point numerical constant.
   - [`RepeatingDecimalNumber.fs`](RepeatingDecimalNumber.fs) – consists of representing a number whose decimal places repeat infinitely.
 - The representation of any symbolic, general and abstract quantity via
   - [`Atomic.fs`](Atomic.fs) – represents any element as a non-interpreted function or constant.
 - Representing and manipulating algebraic expressions via
   - [`SumPow.fs`](SumPow.fs) – represents a general algebraic field.
 - Representing and manipulating polynomial expressions via
   - [`Polynomial.fs`](Polynomial.fs) – represents univariate and multivariate general polynomials whose coefficients are in SumPow.
 - Represent and manipulate matrices, vectors and tensor expressions via
   - [`MultiLinearAlgebra.fs`](MultiLinearAlgebra.fs) – represent and manipulate matrices, vectors and tensor expressions.
 - Perform numerical operations via
   - [`Constant.fs`](Constant.fs) by nature.
   - [`SumPow.fs`](SumPow.fs) using `NumericEvaluation`.
   - [`Polynomial.fs`](Polynomial.fs) using `NumericEvaluation`.
   - [`MultiLinearAlgebra.fs`](MultiLinearAlgebra.fs) using `NumericEvaluation`.

## Current considerations

### Constant values
 - Liyh does not currently implement algebra on arbitrary precision numbers and implements any arithmetic operation (on constants) via `double` (64 bits) and/or via `Complex` (2x 64 bits).

### Overall performance
 - Liyh's kernel isn't highly optimised and misses out on certain optimisations to improve readability and usability. However, the algorithms used and their implementation are written well enough (a priori) not to result in poor performance.

 - The Liyh kernel, and in particular everything to do with [`SumPow.fs`](SumPow.fs) (including all the contents of the file), is highly mutually recursive, which can have an impact on performance.

 - Searching for fixed points in simplifications can slow down execution.

 - Parallelism is only used to generate large quantities of numerical data (in particular to generate graphs).

### Simplification vs. reduction
 - The simplifications consist of calculate algebraically (and therefore symbolically) the expressions that can be mutually or individually transformed into a simpler expression. For example `a + a = 2a`, `Sqrt[8] = 2*Sqrt[2]` or `16/12 = 8/6`.

 - Reductions include simplifications and add more sophisticated simplifications/rewritings, generally involving theorems or identities. For example, `Cos[a]² + Sin[a]² = 1`. Reductions also depend on a given context (a context is a set of equalities or inequalities that certain variables must respect).

### Equality
 - The equality of expressions is generally a difficult and sometimes undecidable problem. The kernel implements equality in a syntactic, albeit slightly more general, way.

 - Expressions that are equal but syntactically quite different are not currently handled well.
