Compi
=====

On this work we describe the implementation of a compiler for an imperative
language with support for classes, approaching the different phases of the
compiler: lexical analysis, parsing, static checks, code generation to an
intermediate code and finally the code generation to machine code.

The implementation was made on Haskell using a compiler phase-driven modularization.

# Dependencies

* base       >= 4.7.0
* parsec     >= 3.1.0
* containers >= 0.6.0
* mtl        >= 2.2.0
* pretty     >= 1.1.3.6
* filepath   >= 1.4.0
* process    >= 1.6.5.0

# Installation

### Using *stack* (Recommended)

1. `stack setup`
2. `stack build`

### Using cabal

1. `cabal configure`
2. `cabal build`
3. `cabal install`

### Using GHC

`ghc --make Main`

# Usage with stack

```
$stack exec -- compi [options]

Options: 

  -i <input>    --input=<input>  Name of the file <input>
  -o <output>   --output=<output>  Rename the exe with <output>
  -t <phase>    --target=<phase>   <phase> es la de "parse", "staticcheck",
     				   "codinter", "assembly" o "executable".
                                   The compilation proceeds until the given phase.
  -h            --help             Show the current information..
```

# Examples

* Ejemplos/selectionSort.compi: Selection Sort implementation using
  many internal and external functions.
