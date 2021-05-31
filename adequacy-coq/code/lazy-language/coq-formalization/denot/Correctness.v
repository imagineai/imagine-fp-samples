(** * Correctness: The compiler correctness theorem *)
Add LoadPath "./domain-theory".
Set Automatic Coercions Import.
Require Import OpApprox.
Require Import DenApprox.
Require Import Source.
Require Import Target.
Require Import Compiler.
Require Import Sequences.
Require Import Denot.
Require Import PredomCore.
Require Import PredomLift.
Set Implicit Arguments.

(** Compiler correctness theorem *)
Theorem compiler_correctness:
  forall t : term nil ty_int,
    let g : closure := [compile t, nil] in
    let w : conf := (g, nil) in
    (term_denot t tt =-= PBot -> diverges w) /\
    (forall m, term_denot t tt =-= Val m -> converges_to w m).
Proof.
  intros.
  split.
  intro Q.
  exact (@correctness_int_divergent t Q nil).
  intros m Q.
  exact (@correctness_int_convergent t m Q).   
Qed.