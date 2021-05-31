Implementation of an agda library for universal algebra, containing main definitions and basic results. 
All this development was published in the journal Electronic Notes in Theoretical Computer Science. 
It’s the first library of UA in Agda. 

Interesting aspects:
* We provide a novel representation of heterogeneous algebras using indexed types.

```
record Signature : Set₁ where
  field
    sorts  : Set
    ops    : (List sorts) × sorts → Set
```

The operations are represented by a family indexed by the arities. This definition gives a lot of benefits 
for defining type-safe properties and results: the arity of an operation is embedded in its type.

Article: https://www.sciencedirect.com/science/article/pii/S1571066118300768
