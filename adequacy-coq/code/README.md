
*** Mechanization of my PhD thesis ***

Authors: Alejandro Gadea and Miguel Pagano.

This development corresponds to the full mechanization in Coq of the chapters 4
and 5 of my PhD thesis: "Biortogonalidad para Corrección de Compiladores y
Adecuación Computacional".

This README file contains instructions to install Coq 8.8.1 and a description
of the modules.

** Installation **

The formalization was tested on Ubuntu with Coq 8.8.1.

* How to install emacs+Coq+PG+CQ:

- Install emacs
- Install 'Coq-8.8.1'       from https://coq.inria.fr/news/coq-881-is-out.html
- Install 'SSreflect 1.6.1' from http://math-comp.github.io/math-comp
- Install 'ProofGeneral'    from https://proofgeneral.github.io/download
- Install 'Company-coq'     from https://github.com/cpitclaudel/company-coq

** Modules **

The formalization of the *chapter 4* is modularized in these files:

- cbv-language/domain-theory/
  Mechanization of Domain Theory developed by Benton, Kennedy, and Varming
- cbv-language/extended-cbn/
  Mechanization of Biorthogonality and Step-Indexed by Rodriguez

- cbv-language/formalization/
### Language ###
-- Lang.v
   Syntax definition of the language
-- Types.v
-- ExSem.v
   Extrinsic denotational semantics for the language
-- InSem.v
   Intrinsic denotational semantics for the language
-- OperSem.v
   Operational semantics for the language

### Adequacy ###
-- OperApprox.v
   Operational approximation for values and expressions
-- DenoApprox.v
   Denotational approximation for values and expressions   
-- Adequacy.v
   Complete results of adequacy
-- fib_Adequacy.v
   Example of the application of adequacy for prove the
   adequacy of fibonacci.

### Meaning of Types / Bracketing ###
-- StrictExt.v
   Strict Extension of Relations
-- EmbProjPair.v
   Embedding-projections pairs
-- MoT.v
   Complete results of bracketing
-- CoherenceExample.v
   Example of the application of coherence.

### Domain Theory extensions ###
-- Domains.v
-- PredomProd.v
-- DomainStuff.v
-- Utils.v

The formalization of the *chapter 5* is modularized in these files:

- lazy-language/coq-formalization/denot/
  -- Mechanization of Domain Theory developed by Benton, Kennedy, and Varming
  -- Mechanization of Biorthogonality and Step-Indexed by Rodriguez

- lazy-language/coq-formalization/lazy/
#### High-Level Language ####
- *Syntax.v*,
  Syntax definition of the language and the type system
- *Semantics.v*,
  Intrinsic denotational semantics for the language

#### The Abstract Machine ####
- *Machine.v*,
  Syntax and transition rules of the abstract machine
- *Map.v*
  A lot of properties about the heaps.

#### Correctness of the Compiler ####
- *Obs.v*,
  Definition of Observation for the denotational approximation.
- *ObsSI.v*, 
  Definition of a Step-Indexed Observation for the operational approximation.
- *Biorthogonality.v*,
  General definition of biorthogonality
- *Compiler.v*,
  Definition of the compiler
- *DenoApprox.v*,
  Definition of realizers, tests and the proof of the fundamental lemma of
  logical relations that help to the proof of correctness of the compiler for
  convergent expressions.
- *OperApprox.v*,
  Definition of realizers, tests and the proof of the fundamental lemma of
  logical relations that help to the proof of correctness of the compiler for
  divergent expressions.
  
** Using the library **

You can type-check the full mechanization of the *chapter 4* from the command
line:
    $ cd cbv-language/domain-theory
    $ make
    $ coqc domoprs.v
    $ cd ../extended-cbn
    $ make
    $ cd ../formalization
    $ make

You can type-check the full mechanization of the *chapter 5* from the command
line:
    $ cd lazy-language/coq-formalization/denot/domain-theory
    $ make
    $ coqc domoprs.v
    $ cd ../
    $ make
    $ cd ../lazy
    $ make
    
Alternatively, you can load any file in emacs and type-check it with
the command "C-c C-b"

A reference with commands to edit, type check and compile Coq code in emacs
is available here:
https://proofgeneral.github.io/doc/userman/ProofGeneral_12/#Coq_002dspecific-commands
