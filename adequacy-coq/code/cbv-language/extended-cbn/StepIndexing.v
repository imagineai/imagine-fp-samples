(** * StepIndexing: Step-indexed sets *)
Set Automatic Coercions Import.
Require Import Integers.
Require Import Setoid.
Require Import Basics.
Require Import Datatypes.
Require Import Biorthogonality.
Require Import Rel.
Require Import Sets.
Set Implicit Arguments.

Open Scope nat_scope.
Open Scope type_scope.

(** Step-indexed family of sets *)
Record StepI (A : Type) (r : iSet A) := stepi {
                                            (* zero is not used yet *)
         zero : Same_set _ (r 0) (Full_set A) ;
         decreasing : forall i : nat, Included _ (r (S i)) (r i)
}.                 

Lemma stepi_decreasing :
  forall A r,
  StepI (r : iSet A) ->
  forall j i, i <= j -> Included _ (r j) (r i).
Proof.
  intros A r si.
  induction j.
  intros i ?.
  assert (i = 0) as P.
  auto with arith.
  rewrite P.
  eapply Included_reflexive.
  intros i Q.
  destruct (le_or_lt i j).
  eapply Included_transitive.
  eapply (decreasing si j).
  eapply (IHj i). auto.
  assert (i = S j) as P.
  auto with arith.
  rewrite <- P.
  eapply Included_reflexive.
Qed.

(** Indexed type *)
Definition Indexed (A:Type) := nat * A.

(** Down-closed indexed set *)
Definition down_closed (A : Type) (X : Ensemble (Indexed A)) :=
  forall a i j, In _ X (i, a) -> j <= i -> In _ X (j, a).

Definition mrel (A B : Type) (r : iRel A B) : Rel (Indexed A) (Indexed B) :=
  fun ia => 
    fun jb =>
      match ia with
          (i, a) =>
          match jb with
              (j, b) => r (min i j) a b 
          end
      end.

Definition mrel_left (A B : Type) (r : iRel A B) : Rel (Indexed A) (Indexed B) :=
  fun ia =>
    fun jb =>
      match ia with
          (i, a) =>
          match jb with
              (j, b) => i <= j -> r i a b
          end
      end.

Definition mrel_right (A B : Type)(r : iRel A B) : Rel (Indexed A) (Indexed B) :=
  fun ia =>
    fun jb =>
      match ia with
          (i, a) =>
          match jb with
              (j, b) => j <= i -> r j a b
          end
      end.

(** Combining step-indexed sets with orthogonal operators *)

Lemma bbot_weakened:
  forall A B (r : iRel A B),
  forall X : Ensemble (Indexed A),
    down_closed X ->
    Same_set _ (bbot (mrel r) X) (bbot (mrel_left r) X).
Proof.
  intros A B r X dc.
  unfold Same_set.
  split ;
  intros jb jbmX ;
  destruct jb as (j , b).
  (* => *)
  intros ia iaX.
  destruct ia as (i, a).
  intro ilej.
  unfold In in *.
  unfold bbot in *.
  unfold mrel in *.
  replace i with (min i j).
  eapply (jbmX (i, a) iaX).
  eapply min_l. auto.
  (* <= *)
  intros ia iaX.
  destruct ia as (i, a).
  unfold In in jbmX.
  unfold bbot in *.
  unfold mrel in *.
  unfold mrel_left in *.
  destruct (le_or_lt i j) as [ileqj | igtj].
  replace (min i j) with i.
  eapply (jbmX (i, a) iaX ileqj).
  apply eq_sym.
  apply min_l. auto.
  assert (In (Indexed A) X (j, a)) as jaX.
  eapply dc. eauto.
  apply lt_le_weak. auto.
  replace (min i j) with j.
  eapply (jbmX (j, a) jaX (le_refl _)).
  apply eq_sym. 
  apply min_r.
  apply lt_le_weak.
  auto.
Qed.

(* bbtop (mrel r) X is down-closed when r is step-indexed *)
Lemma bbot_dc:
  forall A B, 
  forall r : iRel A B,
    StepI (irel_reli r) ->
    forall X : Ensemble (Indexed A),
      down_closed (bbot (mrel r) X).
Proof.
  intros A B r si X.
  unfold down_closed.
  intros b i j H jleqi.
  intro ka.
  destruct ka as (k, a).
  intro kaX.
  specialize (H _ kaX).
  unfold mrel in *.
  rewrite rel_equiv.
  rewrite rel_equiv in H.
  assert (min k j <= min k i).
  apply PeanoNat.Nat.min_glb.
  apply PeanoNat.Nat.le_min_l.
  eapply le_trans.
  apply PeanoNat.Nat.le_min_r.
  auto.
  eapply (stepi_decreasing si). eauto.
  eauto.
Qed.

Lemma bbot_same_morphism:
  forall A B (r : Rel A B) (X Y : Ensemble A),
    Same_set _ X Y ->
    Same_set _ (bbot r X) (bbot r Y).
Proof.
  intros A B r X Y.
  intros S0.
  split ;
  intros b L1 ;
  intros y L2 ;
  apply L1 ;
  apply S0 ;
  auto.
Qed.

Lemma btop_same_morphism:
  forall A B (r : Rel A B) (X Y : Ensemble B),
    Same_set _ X Y ->
    Same_set _ (btop r X) (btop r Y).
Proof.
  intros A B r X Y.
  intros S0.
  split ;
  intros b L1 ;
  intros y L2 ;
  apply L1 ;
  apply S0 ;
  auto.
Qed.

Add Parametric Morphism (A B : Type) (r : Rel A B) : (bbot r)
with signature (@Same_set A) ==> (@Same_set B)
as bbot_same_morphism_.
Proof.
  intros X Y.
  apply (bbot_same_morphism).
Qed.

Add Parametric Morphism (A B : Type) (r : Rel A B) : (btop r)
with signature (@Same_set B) ==> (@Same_set A)
as btop_same_morphism_.
Proof.
  intros X Y.
  apply (bbot_same_morphism).
Qed.

Lemma bbot_morphism:
  forall A B (r1 r2 : Rel A B) (X : Ensemble A),
    Same_rel r1 r2 ->
    Same_set _ (bbot r1 X) (bbot r2 X).
Proof.
  intros A B r1 r2 X.
  intros H.
  unfold Same_rel in H.
  unfold Same_set.
  unfold Included.
  unfold bbot.
  unfold In.
  split ;
  intros ;
  first [
      rewrite <- H |
      rewrite H
    ] ;
  auto.
Qed.

Lemma btop_morphism:
  forall A B (r1 r2 : Rel A B) (X : Ensemble B),
    Same_rel r1 r2 ->
    Same_set _ (btop r1 X) (btop r2 X).
Proof.
  intros A B r1 r2 X.
  intros H.
  unfold Same_rel in H.
  unfold Same_set.
  unfold Included.
  unfold btop.
  unfold In.
  split ;
  intros ;
  first [
      rewrite <- H |
      rewrite H
    ] ;
  auto.
Qed.

Definition bbot_flip A B (X : Ensemble A) (r : Rel A B) := bbot r X.
Definition btop_flip A B (X : Ensemble B) (r : Rel A B) := btop r X.

Hint Unfold bbot_flip btop_flip.

Add Parametric Morphism (A B : Type) (X : Ensemble A) : (@bbot_flip A B X)
with signature (@Same_rel A B) ==> (@Same_set B)
as bbot_morphism_.
Proof.
  intros r1 r2.
  apply (@bbot_morphism A B r1 r2 X).
Qed.

Add Parametric Morphism (A B : Type) (X : Ensemble B) : (@btop_flip A B X)
with signature (@Same_rel A B) ==> (@Same_set A)
as btop_morphism_.
Proof.
  intros r1 r2.
  apply (@btop_morphism A B r1 r2 X).
Qed.

Add Parametric Morphism (A B : Type) : (@transpose A B)
with signature (@Same_rel A B) ==> (@Same_rel B A)
as transpose_morphism.
Proof.
  intros.
  unfold Same_rel in *.
  unfold transpose.
  intros.
  rewrite H.
  tauto.
Qed.

Lemma down_closed_same:
  forall A (X Y : Ensemble (Indexed A)),
    Same_set _ X Y ->
    (down_closed X <-> down_closed Y).
Proof.
  intros A X Y.
  intros XY.
  split.
  intro DCX.
  intros a i j aiY jleqi.
  set (InYX := proj2 XY).
  set (InXY := proj1 XY).
  set (iaInX := InYX _ aiY).
  assert (In _ X (j, a)) as jaInX.
  unfold down_closed in DCX.
  eapply DCX ;
  eauto.
  unfold Included in *.
  eauto.
  intro DCX.
  intros a i j aiX jleqi.
  set (InYX := proj2 XY).
  set (InXY := proj1 XY).
  set (iaInX := InXY _ aiX).
  assert (In _ Y (j, a)) as jaInY.
  unfold down_closed in DCX.
  eapply DCX ;
  eauto.
  unfold Included in *.
  eauto.
Qed.

Add Parametric Morphism (A : Type) :  
  (@down_closed A) with signature (@Same_set (Indexed A)) ==> iff
as down_closed_morphism.
Proof.
  intros X Y XY.
  apply down_closed_same.
  auto.
Qed.
  
(* transpose idempotent *)
Lemma transpose_idempotent:
  forall A B (r : Rel A B),
    Same_rel (transpose (transpose r)) r.
Proof.
  intros A B r a b.
  split ;
  intros ;
  unfold transpose in * ;
  auto.
Qed.

Lemma itranspose_idempotent:
  forall A B (r : iRel A B),
    Same_irel (itranspose (itranspose r)) r.
Proof.
  intros A B r a b.
  split ;
  intros ;
  unfold itranspose in * ;
  auto.
Qed.

(* bbot and transpose *)
Lemma bbot_transpose:
  forall A B (r : Rel A B) (X : Ensemble A),
    Same_set _ (bbot r X) (btop (transpose r) X).
Proof.
  intros A B r X.
  split ;
  intros ;
  unfold In in * ;
  unfold bbot in * ;
  unfold btop in * ;
  unfold transpose in * ;
  auto.
Qed.

Lemma btop_transpose:
  forall A B (r : Rel A B) (X : Ensemble B),
    Same_set _ (btop r X) (bbot (transpose r) X).
Proof.
  intros A B r X.
  split ;
  intros ;
  unfold In in * ;
  unfold bbot in * ;
  unfold btop in * ;
  unfold transpose in * ;
  auto.
Qed.

(* mrel and transpose *)
Lemma mrel_transpose:
  forall (A B : Type) (r : iRel A B),
    Same_rel (mrel r) (transpose (mrel (itranspose r))).
Proof.
  intros A B r p q.
  split ; 
  intros ;
  destruct p ;
  destruct q ;
  unfold mrel in * ;
  unfold transpose in *;
  unfold itranspose in * ;
  rewrite (PeanoNat.Nat.min_comm) ;
  auto.
Qed.

Lemma mrel_transpose':
  forall (A B : Type) (r : iRel A B),
    Same_rel (transpose (mrel r)) (mrel (itranspose r)).
Proof.
  intros A B r.
  set (r' := mrel (itranspose r)).
  rewrite <- (transpose_idempotent r').
  eapply transpose_morphism.
  apply mrel_transpose.
Qed.

(* mrel_left, mrel_right and transpose *)
Lemma mrel_right_transpose:
  forall (A B : Type) (r : iRel A B),
  Same_rel (mrel_right r) (transpose (mrel_left (itranspose r))).
Proof.
  intros A B r p q.
  split ;
  intros ;
  destruct p ;
  destruct q ;
  unfold mrel_right in * ;
  unfold mrel_left in * ;
  unfold transpose in * ;
  unfold itranspose in * ;
  auto.
Qed.

Lemma mrel_transpose_right:
  forall (A B : Type) (r : iRel A B),
  Same_rel (transpose (mrel_right r)) (mrel_left (itranspose r)).
Proof.
  intros A B r.
  set (r' := mrel_left (itranspose r)).
  rewrite <- (transpose_idempotent r').
  eapply transpose_morphism.
  apply mrel_right_transpose.
Qed.

(* This may be proved directly without using
bbot_weakened, but I am stubborn and like to transpose things *)
Lemma btop_weakened:
  forall A B (r : iRel A B),
  forall X : Ensemble (Indexed B),
    down_closed X ->
    Same_set _ (btop (mrel r) X) (btop (mrel_right r) X).
Proof.  
  intros A B r X dc.
  rewrite (btop_transpose _).
  rewrite (btop_transpose _).
  fold (bbot_flip X (transpose (mrel r))).
  fold (bbot_flip X (transpose (mrel_right r))).
  rewrite mrel_transpose_right.
  rewrite mrel_transpose'.
  unfold bbot_flip.
  eapply bbot_weakened.
  auto.
Qed.

Lemma transpose_in:
  forall A B,
  forall r : iRel A B,
  forall a : A, 
  forall b : B,
  forall n : nat,
    In _ (irel_reli r n) (a, b) <-> In _ (irel_reli (itranspose r) n) (b, a).
Proof.
  intros A B r a b n.
  split ;
  intro abr ;
  unfold In in * ;
  unfold itranspose ;
  unfold transpose ;
  simpl ;
  auto.
Qed.
  
Lemma stepi_transpose:
  forall A B,
  forall r : iRel A B,
    StepI (irel_reli r) ->
    StepI (irel_reli (itranspose r)).
Proof.
  intros A B r si.
  destruct si as [zero decr].
  econstructor.
  (*zero*)
  split.
  eapply Included_fullset.
  intro ba. 
  destruct ba as (b, a).
  intro inBA.
  rewrite <- transpose_in.
  set (zero' := proj2 zero).
  eapply zero'.
  constructor.
  (*dec*)
  intro i.
  intro ba.
  destruct ba as (b, a).
  intro baIn.
  rewrite <- transpose_in.
  eapply (decr i).
  rewrite transpose_in.
  auto.
Qed.

Lemma btop_dc:
  forall A B, 
  forall r : iRel A B,
    StepI (irel_reli r) ->
    forall X : Ensemble (Indexed B),
      down_closed (btop (mrel r) X).
Proof.
  intros.
  rewrite (btop_transpose (mrel r)).
  fold (bbot_flip X (transpose (mrel r))).
  rewrite (mrel_transpose').
  unfold bbot_flip.
  eapply bbot_dc.
  eapply stepi_transpose.
  auto.
Qed.

Lemma bbot_empty:
  forall A B,
  forall r : Rel A B,
    Same_set _ (bbot r (Ensembles.Empty_set _ )) (Full_set B).
Proof.
  intros.
  split ;
  repeat intro.
  constructor.
  destruct H0.
Qed.

Lemma btop_empty:
  forall A B,
  forall r : Rel A B,
    Same_set _ (btop r (Ensembles.Empty_set _ )) (Full_set A).
Proof.
  intros.
  split ;
  repeat intro.
  constructor.
  destruct H0.
Qed.

Lemma bbot_full:
  forall A B,
  forall (r : Rel A B),
    (exists a, forall b, ~ r a b) ->
    Same_set _ (bbot r (Full_set A)) (Ensembles.Empty_set B).
Proof.
  intros A B r E.
  split.
  intros b Q.
  destruct E as [a E].
  unfold In in Q.
  unfold bbot in Q.
  specialize (E b).
  specialize (Q a).
  contradict E.
  apply Q.
  constructor.
  intros b Q.
  destruct Q.
Qed.
