Overview
================================================

This package provides a simplified abstract structure tree (AST) for
Accelerate's internal language. It uses fewer features of the Haskel
type system than the full AST.  This should make it easier to
understand and easier to use (especially for less experienced Haskell
programmers). However, be aware that the simplicity comes at a price,
and that price is to have fewer static guarantees about the
correctness of your backend code — i.e., some mistakes will not be
caught by the type-checker at backend compile time, but will instead
manifest as exceptions at user-code runtime (as Accelerate is a
runtime compiler). Nevertheless, even if you plan on eventually using
the full AST, the simplified AST may be a great place to get started.

For details on Accelerate, refer to the [main repository][GitHub].

  [GitHub]: https://github.com/AccelerateHS/accelerate


Details
================================================

Actually this package provides more than one intermediate language
spanning between the abstract, purely function Accelerate language,
and a concrete CUDA/OpenCL-like language.

Further, this package includes a number of compiler passes that lower between
representations and perform optimizations.  Accelerate backends that are built
with this "kit" can only a prefix of these compiler passes and stop where they
like to have their own backend take over.

What follows is a brief description of the three main IRs provided by this
package.  For more documentation, refer to the Haddocks of the relevant modules.


Intermediate Language 1: Simplified Accelerate
----------------------------------------------

    Data.Array.Accelerate.IRTypes.SimpleAcc


Intermediate Language 2: C-like for easier code emission
--------------------------------------------------------

    Data.Array.Accelerate.IRTypes.CLike


Intermediate Language 3: C-like for easier code emission
--------------------------------------------------------

    Data.Array.Accelerate.IRTypes.GPUIR

