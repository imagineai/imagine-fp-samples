(** * PredomNary : N-ary morphisms *)
Add LoadPath "./domain-theory".
Set Automatic Coercions Import.
Require Import Arith.
Require Import Common.
Require Import Util.
Require Import PredomAll.
Require Import CCC.
Set Implicit Arguments.
Unset Strict Implicit.

(** Auxiliary constructions *)

Definition pow_morph {Cat : expCat} (A B C : Cat) (f : A =-> B) : 
  (C -=> A) =-> (C -=> B) := exp_fun (f << ev).

(* curry was defined in the lib for the CPO cat only
   uncurry was defined as a function and not as an arrow like here *)
Definition curry {Cat : expCat} (A B C : Cat) :
  (A * B -=> C) =-> (A -=> (B -=> C)) 
  := exp_fun (exp_fun (ev << prod_assoc _ _ _)).

Definition uncurry {Cat : expCat} (A B C : Cat) :
  (A -=> (B -=> C)) =-> (A * B -=> C) :=
  exp_fun ((ev << ev >< Id) << prod_assocI _ _ _).

Lemma fmon_leq_elim:
  forall (P Q : cpoType),
  forall (f f' : P =-> Q), 
    f <= f' -> 
    forall x, f x <= f' x.
Proof.
  intros P Q f f' I.
  eapply I.
Qed.

(** N-ary morphism *)
Fixpoint nmorph {C: expCat} (A : C) n (B : C) : C :=
  match n with
      0 => B
    | S n => A -=> nmorph A n B
  end.

(** Finite products *)
Fixpoint nprod {C : cartesianClosedCat} (A : C) n : C :=
  match n with
      0 => One
    | S n => A * nprod A n
  end.

(** Generalized curry *)
Fixpoint ncurry {C : cartesianClosedCat} (A B : C) n 
: (nprod A n -=> B) =-> (nmorph A n B) :=
  match n as n0 return (nprod A n0 -=> B) =-> (nmorph A n0 B) with
    | O   => ev << <| Id , terminal_morph ((One : C) -=> B) |>  
    | S n => pow_morph _ (ncurry A B n) << curry _ _ _
  end.

(** Generalized uncurry *)
Fixpoint nuncurry {C : cartesianClosedCat} (A B : C) n 
: (nmorph A n B) =-> (nprod A n -=> B) :=
  match n as n0 return (nmorph A n0 B) =-> (nprod A n0 -=> B) with
    | 0 => exp_fun pi1
    | S n => uncurry _ _ _ << pow_morph _ (nuncurry A B n)
  end.

(** Apply once *)
Definition nstep (A B : cppoType) (a : A) n : nmorph A (S n) B -=> nmorph A n B
:= ev << SWAP << PAIR _ a.

(** Full application *)
Fixpoint nmorph_fapply (A B : cppoType) n (args : Vector.t A n) : 
  nmorph A n B =-> B :=
match args in (Vector.t _ n0) return nmorph A n0 B =-> B with
    Vector.nil => Id
  | Vector.cons a _ args' => @nmorph_fapply _ _ _ args' << @nstep _ _ a _
end.

Require Import Coq.Program.Equality.
Require Import Vector.

(** Partial order of vectors *)
(* TODO: define a cpo of vectors *)
Definition vector_leq (A : cpoType) n : t A n -> t A n -> Prop :=
  fun v v' => Vector.Forall2 (fun a a' => a <= a') v v'.

Definition vector_eq (A : cpoType) n : t A n -> t A n -> Prop :=
  fun v v' => Vector.Forall2 (fun a a' => a =-= a') v v'.

Lemma vector_eq_sym:
  forall (A : cpoType) n (v v' : t A n),
    vector_eq v v' -> vector_eq v' v.
Proof.
  induction 1.
  econstructor.
  constructor.
  symmetry. auto.
  eauto.
Qed.

Lemma vector_eq_leq:
  forall (A : cpoType) n (v v' : t A n),
    vector_eq v v' -> vector_leq v v'.
Proof.
  induction 1.
  econstructor.
  constructor ;
  eauto.
Qed.

(** Generalized monotony *)
Lemma nmorph_monotonic:
  forall (A B : cppoType) n (F : nmorph A n B), 
  forall (v v' : Vector.t A n),
    vector_leq v v' ->
    nmorph_fapply _ v F <= nmorph_fapply _ v' F.
Proof.
  induction 1.
  auto.
  simpl.
  eapply Ole_trans.
  eapply IHForall2.
  eapply fmonotonic.
  eapply fmonotonic.
  eauto.
Qed.

(** Generalized stability *)
Lemma nmorph_stable:
  forall (A B : cppoType) n (F : nmorph A n B), 
  forall (v v' : Vector.t A n),
    vector_eq v v' ->
    nmorph_fapply _ v F =-= nmorph_fapply _ v' F.
Proof.
 intros A B n F v v' Q.
 split ;
 eapply nmorph_monotonic ;
 eapply vector_eq_leq ;
 auto.
 eapply vector_eq_sym.
 auto.
Qed.  

(** Least upper bound of a vector of chains *)
Definition lub_vec n (A : cpoType) (v : t (natO =-> A) n) : t A n :=
  Vector.map (@lub _) v.

Definition nmorph_fapply_seq n (A B : cppoType) (F : nmorph A n B) 
           (v : t (natO =-> A) n) (i : natO) : B :=
  nmorph_fapply _ (Vector.map (fun (c : natO =-> A) => c i) v) F.

Lemma nmorph_fapply_seq_mono n (A B : cppoType) (F : nmorph A n B)
      (v : t (natO =-> A) n) :
  monotonic (nmorph_fapply_seq F v).
Proof.
  intros i j Q.
  unfold nmorph_fapply_seq.
  eapply nmorph_monotonic.
  generalize n v j i Q.
  clear.
  induction n ;
  intros v j i Q ;
  dependent destruction v.
  simpl. econstructor.
  simpl. econstructor.
  eapply fmonotonic. auto.
  eapply IHn. auto.
Qed.

Definition nmorph_fapply_chain n (A B : cppoType) (F : nmorph A n B)
           (v : t (natO =-> A) n) 
  := mk_fmono (nmorph_fapply_seq_mono F v).

(** Continuity of application *)

Lemma nmorph_continuous_lt:
  forall (A B : cppoType) n (F : nmorph A n B), 
  forall (v : t (natO =-> A) n),
    lub (nmorph_fapply_chain F v) <= nmorph_fapply _ (lub_vec v) F.
Proof.
  intros A B n F v.
  eapply lub_le.
  intros i.
  simpl.
  unfold nmorph_fapply_seq.
  eapply nmorph_monotonic.
  generalize n v.
  clear.
  induction n ;
  intro v ;
  dependent destruction v.
  simpl. econstructor.
  simpl. econstructor.
  eapply le_lub.
  eapply IHn. 
Qed.

Lemma nmorph_continuous_gt:
  forall (A B : cppoType) n (F : nmorph A n B), 
  forall (v : t (natO =-> A) n),
    nmorph_fapply _ (lub_vec v) F <= lub (nmorph_fapply_chain F v).
Proof.
  intros A B.
  induction n ;
  intros F v ;
  dependent destruction v.
  simpl. unfold id.
  match goal with
      |- F <= lub ?E => set (c := E)
  end.
  transitivity (c 0).
  simpl.
  unfold nmorph_fapply_seq.
  simpl. auto.
  eapply le_lub.
  simpl.
  eapply Ole_trans.
  eapply fmonotonic.
  eapply fcontinuous.
  eapply Ole_trans.
  eapply fcontinuous.
  eapply lub_le.
  intro i.
  simpl.
  eapply Ole_trans.
  eapply IHn.
  eapply lub_le.
  intro j.
  simpl.
  unfold nmorph_fapply_seq.
  match goal with
      |- _ <= ?G => set (X := G)
  end.
  set (proj j := fun c : (natO =-> A) => c j).
  set (mapp n (v : t (natO =-> A) n) j := map (proj j) v).
  change (nmorph_fapply _ (@cons _ (h i) _ (mapp _ v j)) F <= X).
  set (k := max i j).
  transitivity (nmorph_fapply _ (@cons _ (h k) _ (mapp _ v k)) F).
  eapply nmorph_monotonic.
  constructor.
  eapply fmonotonic.
  unfold k.
  exact (le_le (Nat.le_max_l i j)).
  generalize n v.
  clear.
  induction n ;
  intros v ;
  dependent destruction v ;
  simpl.
  econstructor.
  constructor.
  unfold proj.
  eapply fmonotonic.
  exact (le_le (Nat.le_max_r i j)).
  eauto.
  change (nmorph_fapply_chain F (@cons _ h _ v) k <= X).
  eapply le_lub.
Qed.

Lemma nmorph_continuous:
  forall (A B : cppoType) n (F : nmorph A n B), 
  forall (v : t (natO =-> A) n),
    nmorph_fapply _ (lub_vec v) F =-= lub (nmorph_fapply_chain F v).
Proof.
  intros A B n F v.
  split.
  eapply nmorph_continuous_gt.
  eapply nmorph_continuous_lt.
Qed.
