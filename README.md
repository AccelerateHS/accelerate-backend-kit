Simplified AST for the Accelerate Array Language
================================================

This package provides a simplified abstract structure tree (AST) for Accelerate's internal language. It uses less type extensions than the full AST. This should make it easier to understand and easier to use (especially for less experienced Haskell programmers). However, be aware that the simplicity comes at a price, and that price is to have less static guarantees about the correctness of your backend code — i.e., some mistakes will not be caught by the type-checker at backend compile time, but will instead manifest as exceptions at user-code runtime (as Accelerate is a runtime compiler). Nevertheless, even if you consider to eventually use the full AST, the simplified AST may be a great place to get started.

For details on Accelerate, refer to the [main repository][GitHub].

  [GitHub]: https://github.com/AccelerateHS/accelerate
