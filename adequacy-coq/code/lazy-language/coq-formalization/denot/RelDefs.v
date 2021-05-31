(** * RelDefs: Relations as sets of configurations *)
Add LoadPath "./domain-theory".
Set Automatic Coercions Import.
Set Implicit Arguments.
Require Import Rel.
Require Import Target.
Require Import Sequences.

(** Closed by anti-execution (with single transition) *)
Definition antiexec (R : Rel closure stack) : Prop :=
  forall g0 g1 s0 s1,
    R g1 s1 -> trans (g0, s0) (g1, s1) -> R g0 s0.

(** Closed by anti-execution *)
Definition antiexec_star (R : Rel closure stack) : Prop :=
  forall g0 g1 s0 s1,
    star trans (g0, s0) (g1, s1) -> R g1 s1 -> R g0 s0.

Lemma antiexec_also_star:
  forall (R : Rel closure stack),
    antiexec R ->
    antiexec_star R.
Proof.
  intros R aE.
  intros g0 g1 s0 s1.
  set (p0 := (g0, s0)).
  set (p1 := (g1, s1)).
  replace g0 with (fst p0) by auto.
  replace s0 with (snd p0) by auto.
  replace g1 with (fst p1) by auto.
  replace s1 with (snd p1) by auto.
  set (P := fun a b => R (fst a) (snd a) -> R (fst b) (snd b)). 
  fold (P p1 p0).
  generalize p0 p1.
  clear - aE.
  induction 1 as [p | p0 p1 p2 H0 H1 Hip].
  unfold P. trivial.
  unfold P in *.
  intro R0.
  specialize (Hip R0).
  destruct p0 as (g0, s0).
  destruct p1 as (g1, s1).
  destruct p2 as (g2, s2).
  simpl in *.
  eapply aE.
  exact Hip.
  exact H0.
Qed.

(** Indexed relation closed by anti-execution *)
Definition iantiexec (R : iRel closure stack) : Prop :=
  forall g0 g1 s0 s1 i,
    R i g1 s1 -> trans (g0, s0) (g1, s1) -> R (S i) g0 s0.

