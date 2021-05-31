This Haskell code was implemented in the context of a phd-course about implementation 
of compilers. We built a compiler of a subset of C++ to Assembly.

Interesting aspects:

* This development divides the implementation of the compiler in phases: 
  - lexical analysis
  - parser 
  - compilation to an intermediate code
  - compilation to machine code.

* The lexer/parser phase was implemented using the Parsec library.

* The native support for defining Abstract Syntax Trees in Haskell 
  allows us to have a clean representation of each language. 
  We define an AST of the source language in src/Syntax, an AST of an 
  intermediate code in src/InterCode and an AST of the Assembly 
  machine code in src/Machine. 

* The intermediate code doesn’t take care of particular memory 
  addresses or registers. It assumes infinite registers with a common 
  abstract representation of memory.

* The last phase compiles from this intermediate language to the Assembly 
  AST, and then to simple text via pretty printing. 
