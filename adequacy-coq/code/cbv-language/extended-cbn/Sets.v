(** * Sets : Some facts about sets *)
Set Automatic Coercions Import.
Require Export Ensembles.
Require Import PredomCore.
Set Implicit Arguments.

(** Power set *)
Definition Power_set (A : Type) := Ensemble A.

Definition reflexive_ := Relation_Definitions.reflexive.

Definition transitive_ := Relation_Definitions.transitive.

Hint Unfold In.
Hint Unfold Included.
Hint Unfold reflexive.
Hint Unfold transitive.
Hint Unfold reflexive_.
Hint Unfold Relation_Definitions.reflexive.
Hint Unfold transitive_.
Hint Unfold Relation_Definitions.transitive.

(** Inclusion as a partial orden *)

Lemma incl_reflexive : forall A : Type, reflexive_ (@Included A).
intros. auto.
Qed.

Lemma incl_transitive : forall A : Type, transitive_ (@Included A).
intros. unfold transitive_. auto.
Qed.

(** Poset of the subsets and inclusion *)
Definition power_set_ord (A : Type) : ordType.
  refine (@OrdType (Power_set A) _).
  refine (@OrdMixin _ (@Included A) _).
  split.
  apply incl_reflexive.
  apply incl_transitive.
Defined.

Lemma Included_reflexive:
  forall A : Type,
    reflexive (Ensemble A) (Included A).
Proof.
  intro A. auto.
Qed.

Lemma Included_transitive : 
  forall A : Type, 
    transitive (Ensemble A) (Included A).
Proof.
  intro A. auto.
Qed.

Lemma Included_fullset:
  forall A : Type,
  forall (X : Ensemble A),
    Included _ X (Full_set A).
Proof.
  intros. intros x inX. 
  constructor.
Qed.

(** Equality of sets *)

Lemma Same_set_reflexive:
  forall A : Type,
    reflexive _ (Same_set A).
Proof.
  intros.
  split ;
  eapply Included_reflexive.
Qed.

Lemma Same_set_transitive:
  forall A : Type,
    transitive _ (Same_set A).
Proof.
  intros.
  intros X Y Z.
  intros XY YZ.
  split.
  eapply Included_transitive.
  eapply (proj1 XY).
  eapply (proj1 YZ).
  eapply Included_transitive.
  eapply (proj2 YZ).
  eapply (proj2 XY).
Qed.

Lemma Same_set_symmetric:
  forall A : Type,
    symmetric _ (Same_set A).
Proof.
  intros.
  intros X Y XY.
  split.
  apply (proj2 XY).
  apply (proj1 XY).
Qed.

Add Parametric Relation (A : Type) : (Ensemble A) (Same_set A)
  reflexivity proved by (@Same_set_reflexive A)
  symmetry proved by (@Same_set_symmetric A)
  transitivity proved by (@Same_set_transitive A) as Same_set_relation.

(** Indexed family of sets *)
Definition iSet (A : Type) := nat -> Ensemble A.