(** * Rel : Some facts about relations *)
Add LoadPath "./domain-theory".

Set Automatic Coercions Import.
Require Import Setoid.
Require Import Sets.
Set Implicit Arguments.

(** Relations *)
Definition Rel (A B : Type) := A -> B -> Prop.

(** Indexed relation *)
Definition iRel (A B : Type) := nat -> Rel A B.

(** Relation transpose *)
Definition transpose (A B : Type) (r : Rel A B) : Rel B A :=
  fun b a => r a b.

(** Indexed transpose *)
Definition itranspose (A B : Type) (r : iRel A B) : iRel B A :=
  fun n => transpose (r n).

(** Equality of relations *)

Definition Same_rel (A B : Type) (r1 : Rel A B) (r2 : Rel A B)
  := forall a b, r1 a b <-> r2 a b.

Definition Same_irel (A B : Type) (r1 : iRel A B) (r2 : iRel A B)
  := forall n, Same_rel (r1 n) (r2 n).

Hint Unfold transpose itranspose Same_rel Same_irel.

Lemma Same_rel_reflexive:
  forall A B, reflexive _ (@Same_rel A B).
Proof.
  intros.
  unfold reflexive.
  unfold Same_rel in *. 
  tauto.
Qed.

Lemma Same_rel_symmetric:
  forall A B, symmetric _ (@Same_rel A B).
Proof.
  intros. 
  unfold symmetric.
  intros x y H.
  unfold Same_rel in *.
  intros.
  rewrite H.
  tauto.
Qed.

Lemma Same_rel_transitive:
  forall A B, transitive _ (@Same_rel A B).
Proof.
  intros.
  unfold transitive.
  intros ? ? ? H0 H1.
  unfold Same_rel in *.
  intros.
  rewrite H0.
  rewrite <- H1.
  tauto.
Qed.

Add Parametric Relation (A B : Type) : (Rel A B) (@Same_rel A B)
  reflexivity proved by (@Same_rel_reflexive A B)
  symmetry proved by (@Same_rel_symmetric A B)
  transitivity proved by (@Same_rel_transitive A B) as Same_rel_relation.

(** Indexed relations as sets *)

Definition Reli (A B : Type) := iSet (A * B).

Coercion irel_reli (A B : Type) (r : iRel A B) : Reli A B :=
  fun i =>
    fun p =>
      match p with 
        | (a , b) => r i a b
      end.

Coercion reli_irel (A B : Type) (r : Reli A B) : iRel A B :=
  fun i a b => In _ (r i) (a, b).

Lemma rel_equiv :
  forall A B (r : iRel A B), 
  forall a b i,
    r i a b <-> In _ ((irel_reli r) i) (a, b).
Proof.
  intros. split ; auto.
Qed.