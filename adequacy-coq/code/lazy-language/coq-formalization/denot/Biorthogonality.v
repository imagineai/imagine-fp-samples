(** * Biorthogonality : Orthogonal operators and Galois Connections *)
Add LoadPath "./domain-theory".
Set Automatic Coercions Import.
Require Import Integers.
Require Import Setoid.
Require Import Basics.
Require Import Rel.
Require Import Sets.
Require Import PredomCore.
Set Implicit Arguments.

(** * Antitone functions  *)

Definition antitone (A B : ordType) (f : A -> B) :=
  forall x y : A, x <= y -> f y <= f x. 

Lemma antitone_stable:
  forall (A B : ordType) (f : A -> B),
    antitone _ _ f -> stable f.
Proof.
  intros A B f am.
  intros a a' eq.
  split ;
  eapply am ;
  auto.
Qed.

(** * Antitone Galois connection *)

Definition GC (A B : ordType) (f : A -> B) (g : B -> A) : Prop :=
  forall a : A, forall b : B, 
    b <= f a <-> a <= g b.

Hint Unfold GC.

(** Some properties of antitone Galois connections *)

Lemma gc_comm : forall A B f g, @GC A B f g -> @GC B A g f.
Proof.
  intros A B f g gc.
  unfold GC in *.
  intros b a. 
  symmetry.
  auto.
Qed.

Lemma gc_prop:
  forall A B f g, 
    @GC A B f g -> 
    forall a, 
      a <= g (f (a)).
Proof.
  intros A B f g gc a.
  rewrite <- (gc a).
  reflexivity.
Qed.

Hint Resolve gc_prop : gc_db.

Lemma gc_antitone:
  forall A B f g,
    @GC A B f g -> antitone _ _ f.
Proof.
  intros A B f g gc.
  intros a a' alea'.
  rewrite (gc a).
  eapply transitivity.
  apply alea'.
  auto with gc_db.
Qed.

Lemma gc_antitone_snd:
  forall A B f g,
    @GC A B f g -> antitone _ _ g.
Proof.
  intros A B f g gc.
  eapply gc_antitone.
  eapply gc_comm.
  auto.
Qed.

Lemma gc_comp :
  forall A B f g,
    @GC A B f g -> 
    forall a, 
      f (g (f (a))) =-= f (a).
Proof.
  Ltac fold_Ole :=
  match goal with
      |- PreOrd.Ole ?C ?x ?y
      => replace (PreOrd.Ole C x y) with (x <= y) by auto
  end.
  intros A B f g gc a.
  split.
  eapply gc_antitone.
  eauto.
  auto with gc_db.
  fold_Ole.
  rewrite (gc _).
  reflexivity.
Qed.

Hint Rewrite gc_comp : gc_db.

(** * Closure operator *)

Record closure_fun (A : ordType) (f : A -> A) :=
  {
    f_extensive : forall a, a <= f (a);
    f_monotonic : monotonic f;
    f_idempotent : forall a, f (f (a)) =-= f (a)
  }.

(** A Galois connection leads to a closure function *)
Lemma gc_closure: 
  forall A B f g,
    GC A B f g -> closure_fun A (compose g f).
Proof.
  intros A B f g.
  intro gc.
  econstructor ;
  unfold compose.
  auto with gc_db.
  intros a b aleb.
  eapply gc_antitone_snd.
  eauto.
  eapply gc_antitone ;
  auto.
  intro a.
  assert (stable g) as g_stable.
  eapply antitone_stable.
  eapply gc_antitone_snd.
  auto.
  eapply g_stable.
  apply gc_comp.
  auto.
Qed.

(** * Relation-generated Galois connections *)

(** The orthogonal operators *)
Definition bbot (A B : Type) (r : Rel A B) : Power_set A -> Power_set B :=
  fun X => fun b : B => forall a : A, In _ X a -> r a b.

Definition btop (A B : Type) (r : Rel A B) : Power_set B -> Power_set A :=
  fun Y => fun a : A => forall b : B, In _ Y b -> r a b.

Definition bclos (A B : Type) (r : Rel A B) : Power_set A -> Power_set A :=
  compose (btop r) (bbot r).

Hint Unfold bbot.
Hint Unfold btop.

(** The orthogonal operators are a Galois connection *)
Lemma gc_generated : 
  forall A B (r : Rel A B), 
    @GC (power_set_ord A) (power_set_ord B) (bbot r) (btop r).
Proof.
  intros A B r.
  intros X Y.
  split.
  intro H1.
  intros a inX.
  intros b inY.
  simpl in H1.
  assert (In _ (bbot r X) b) as H.
  auto.
  auto.
  intro H2.
  intros b inY.
  intros a inX.
  simpl in H2.
  assert (In _ (btop r Y) a) as H.
  auto.
  auto.
Qed.

(** The function bclos is indeed a closure operator *)  
Corollary bclos_clos : 
  forall A B (r : Rel A B),
    closure_fun (power_set_ord A) (bclos r).
Proof.
  intros A B r.
  unfold bclos.
  set (gc := gc_generated r).
  set (H := gc_closure gc).
  auto.
Qed.