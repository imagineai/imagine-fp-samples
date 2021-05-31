This Haskell code was implemented in the context of a project for building 
an interpreter of a very simple “while language” with support of reflection, 
with educational purposes. 
This interpreter is currently used in the course of computability at 
Universidad Nacional de Río Cuarto (Argentina).

This project consists of a tool for helping to understand the concepts included 
in the book “Computability and Complexity” by Neil Jones. 

Interesting aspects:

* The book presents some constructions of the “while” language, and some extensions, 
  in a very informal way, so one of the interesting aspects of this implementation 
  is the concrete formalization of these constructions.

* In this language the programs can be values too, so a program can receive as
  input another program. In `src/ProgAsValue` we define a bijection from programs
  to values, and finally we could implement the interpreter of "while language"
  in the same "while language": src/examples/interp2.xwhile.

