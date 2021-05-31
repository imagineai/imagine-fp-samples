Add Rec LoadPath "." as Top.
Set Automatic Coercions Import.
Set Implicit Arguments.

Require Import Utf8.
Require Export Ensembles.
Require Export Sets.Constructive_sets.
Require Export Coq.Program.Equality.
Require Export Setoid.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Classes.RelationClasses.

(** * Extended Coq.Ensembles *)
(** A few properties about sets and some extremely useful parametric morphisms. *)

Lemma Included_refl:
  forall A X, Included A X X.
Proof.
  firstorder.
Qed.

Lemma Included_trans:
  forall A X Y Z, Included A X Y -> Included A Y Z -> Included A X Z.
Proof.
  firstorder.
Qed.

Add Parametric Relation A : (Ensemble A) (Included A)
    reflexivity proved by (@Included_refl A)
    transitivity proved by (@Included_trans A)
      as included_set_rel.

Add Parametric Morphism A (X : Ensemble A) : (Included A X) with
    signature Same_set A ==> iff as included_same_left_mor.
Proof.
  firstorder.
Qed.

Add Parametric Morphism A (Y: Ensemble A) : (fun X => Included A X Y) with
    signature Same_set A ==> iff as included_same_right_mor.
Proof.
  firstorder.
Qed.

Lemma Same_set_refl:
  forall A X , Same_set A X X.
Proof.
  firstorder.
Qed.

Lemma Same_set_sym:
  forall A X Y , Same_set A X Y -> Same_set A Y X.
Proof.
  firstorder.
Qed.

Lemma Same_set_trans:
  forall A X Y Z, Same_set A X Y -> Same_set A Y Z -> Same_set A X Z.
Proof.
  firstorder.
Qed.

Lemma Same_set_in_iff:
  forall A X Y, Same_set A X Y <-> (forall k, In A X k <-> In A Y k).
Proof.
  intros A X Y.
  split.
  intro S.
  split ; eapply S.
  intro H.
  split ;
  intros k ;
  eapply H.
Qed.

Lemma Union_in_iff:
  forall A X Y p, In A (Union A X Y) p <-> In A X p \/ In A Y p.
Proof.
  intros A X Y p.
  split.
  intro I.
  destruct I.
  left. auto.
  right. auto.
  intros.
  destruct H.
  eapply Union_introl.
  auto.
  eapply Union_intror.
  auto.
Qed.

Add Parametric Relation A : (Ensemble A) (Same_set A)
    reflexivity proved by (@Same_set_refl A)
    symmetry proved by (@Same_set_sym A)
    transitivity proved by (@Same_set_trans A)
      as same_set_rel.

Add Parametric Morphism A : (Union A) with
    signature (Same_set A) ==> (Same_set A) ==> (Included A) as union_same_included_mor.
Proof.
  intros X Y EQ.
  intros Z W EQ'.
  intros a I.
  rewrite Union_in_iff.
  rewrite Union_in_iff in I.
  destruct EQ  as [INC1 INC2].
  destruct EQ' as [INC3 INC4].
  destruct I as [H1 | H2]. 
  specialize (INC1 _ H1).
  left. auto.
  specialize (INC3 _ H2).
  right. auto.
Qed.

Add Parametric Morphism A : (Union A) with
    signature (Same_set A) ==> (Same_set A) ==> (Same_set A) as union_same_mor.
Proof.
  intros Γ Δ EQ Γ' Δ' EQ'.
  split ;
  eapply union_same_included_mor ;
  auto.
  symmetry.
  auto.
  symmetry.
  auto.
Qed.

Add Parametric Morphism A : (Included A) with
    signature Same_set A ==> Same_set A ==> iff as included_mor.
Proof.
  intros X Y EQ1 X' Y' EQ2.
  unfold Included.
  rewrite Same_set_in_iff in EQ1.
  rewrite Same_set_in_iff in EQ2.
  firstorder.
Qed.

Ltac included_left_rewrite H :=
  match goal with
  | [ |-  Included ?Z ?X ?Y ] => pattern X ; rewrite H
  end.

Ltac included_right_rewrite H :=
  match goal with
  | [ |-  Included ?Z ?X ?Y ] => pattern Y ; rewrite H
  end.

Lemma union_included:
  forall A X Y Z, Included A X Z -> Included A Y Z -> Included A (Union A X Y) Z.
Proof.
  intros A X Y Z H1 H2.
  intros x H3.
  destruct H3 ;
    eauto.
Qed.

Lemma Union_comm:
  forall A X Y, Same_set _ (Union A X Y) (Union A Y X).
Proof.
  intros A X Y.
  rewrite Same_set_in_iff.
  intro k.
  repeat rewrite Union_in_iff.
  tauto.
Qed.

Lemma Union_assoc:
  forall A X Y Z, Same_set _ (Union A (Union A X Y) Z) (Union A X (Union A Y Z)).
Proof.
  intros A X Y Z.
  rewrite Same_set_in_iff.
  intro k.
  repeat rewrite Union_in_iff.
  tauto.
Qed.

Lemma Union_idem:
  forall A X, Same_set _ (Union A X X) X.
Proof.
  intros A X.
  rewrite Same_set_in_iff.
  intro k.
  rewrite Union_in_iff.
  tauto.
Qed.

Lemma Union_subset:
  forall A X Y,
    Included A X Y ->
    Same_set _ (Union A X Y) Y.
Proof.
  intros A X Y IN.
  rewrite Same_set_in_iff.
  intro k.
  repeat rewrite Union_in_iff.
  firstorder.
Qed.

Lemma Included_Union_1:
  forall A X Y, Included _ X (Union A X Y).
Proof.
  intros.
  intros k.
  rewrite Union_in_iff.
  tauto.
Qed.

Lemma Included_Union_2:
  forall A X Y, Included _ Y (Union A X Y).
Proof.
  intros.
  intros k.
  rewrite Union_in_iff.
  tauto.
Qed.

Lemma Included_Singleton:
  forall A X p, Included A (Singleton _ p) X <-> In _ X p.
Proof.
  intros A X p.
  split.
  intro I.
  specialize (I p).
  eapply I.
  constructor.
  intro P.
  intros a I'.
  destruct I'.
  auto.
Qed.