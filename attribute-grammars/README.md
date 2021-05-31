Attribute Grammars

This Haskell code was implemented in the context of a 1 week course
about Attribute Grammars at Universidad de la República (Uruguay). We
implemented two examples of use of attribute grammars: the repmin
problem and type inference for lambda calculus.

We used a DSL built on top of Haskell, for using attribute grammars. 
Each AST is defined together with attributes specifying semantics.
In `code/LambdaCalculus/Lambda.ag` we define the AST for lambda calculus
together with the semantics for type inference. 
