Require Import ZArith.

Inductive BOp := PlusBOp | MinusBOp.

Definition semZBOp (bop : BOp) : Z -> Z -> Z :=
  match bop with
  | PlusBOp  => Z.add
  | MinusBOp => Z.sub
  end
.
