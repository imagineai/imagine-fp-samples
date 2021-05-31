In this project we are building a code generator for building web applications, in Haskell. 
We had to design a high-level language representing different aspects of an application. 
From this language we generate backend code of different frameworks like Django and Node-express. 

Interesting aspects:
* We designed an abstract representation of an “Imagine specification”. This specification captures 
  the input of the code generator, necessary to build a complete backend application depending on 
  the choice of a framework and other settings. See `code/ImagineSpec.hs`

* We support two different concrete syntax: a text-based syntax and a json-based syntax, 
  used in a web Graphical User Interface. We manage the different concrete input syntax with a typeclass.
  See `code/ImagineCompiler.hs`

* For the text-based version, we used tools “Alex” and “Happy” in the implementation of lexer and parsing.

* We implemented a static checker using monad transformers. See `code/StaticChecksMonad.hs`

* We use a template-approach for generating files, using mustache templates and filling the holes with 
  information coming from the input spec.


