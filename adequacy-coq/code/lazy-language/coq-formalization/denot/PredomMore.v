(** * PredomMore : Extension of the domain-theory library *)
Add LoadPath "./domain-theory".
Set Automatic Coercions Import.
Require Import Arith.
Require Import Common.
Require Import Util.
Require Import PredomAll.
Require Import PredomNary.
Require Import CCC.
Require Import Vector.
Unset Strict Implicit.
Import VectorDef.VectorNotations.
Open Scope vector_scope.
Delimit Scope vector_scope with V.

(** * Cpos are cartesian closed categories *)

(** Cpo is cartesian closed *)
Canonical Structure cpoCartesianClosedMixin 
  := CartesianClosedCat.Mixin cpoTerminalMixin.
Canonical Structure cpoCartesianClosedType
  := Eval hnf in cartesianClosedCatType cpoCartesianClosedMixin.

(** Cpo is cartesian closed *)
Canonical Structure cppoCartesianClosedMixin
  := CartesianClosedCat.Mixin cppoTerminalMixin.
Canonical Structure cppoCartesianClosedType
  := Eval hnf in cartesianClosedCatType cppoCartesianClosedMixin.


(** * Results about chains *)

Lemma chain_suc:
  forall (O : cpoType) (c : natO -> O),
    (forall i, c i <= c (S i)) ->
    monotonic c.
Proof.
  intros O c F.
  unfold monotonic.
  intros x y Q.
  set (Q' := leP Q).
  clearbody Q'. clear Q.
  generalize y x Q'.
  induction 1.
  auto.
  eapply Ole_trans.
  eauto.
  eauto.
Qed.

(** Constant chain *)
Definition chain_cte (O : ordType) (c : natO =-> O) (x : O) :=
  forall i, c i =-= x.

(** All chains of a discrete order are constant *)
Lemma dis_chain_cte 
      (D : Type) (c : natO =-> discrete_ordType D) :
      chain_cte _ c (c 0).
Proof.
  intro i.
  set (L := fmonotonic c).
  unfold monotonic in L.
  specialize (L _ _ (leq0n i)).
  auto.
Qed.

(** * Results about least upper bounds *)

(** The [lub] of any constant chain is the constant itself *)
Lemma lub_cte_chain (O : cpoType) (c : natO =-> O) (x : O) :
  chain_cte _ c x -> (lub c =-= x).
Proof.
  intro Q. 
  unfold chain_cte in Q.
  split.
  eapply lub_le.
  intro n.
  specialize (Q n).
  rewrite Q.
  auto.
  specialize (Q 0).
  rewrite <- Q.
  eapply le_lub.
Qed.

Lemma lub_le_compat_weak (O : cpoType):
  forall (c c' : natO =-> O),
    (forall i, exists j, c i <= c' j) -> lub c <= lub c'.
Proof.
  intros c c' P.
  eapply lub_le.
  intro i.
  specialize (P i).
  destruct P as [j Q].
  transitivity (c' j).
  auto.
  eapply le_lub.
Qed.

Lemma lub_eq_compat2 (O : cpoType):
  forall (c : natO =-> O) x,
    (forall n : nat, c n =-= x) ->
    lub c =-= x.
Proof.
  intros c x P.
  split.
  eapply lub_le.
  intro n.
  eapply P.
  transitivity (c 0).
  rewrite (P 0).
  eapply Ole_refl.
  eapply le_lub.
Qed.

(** * Results about discrete cpos *)

(** Discrete cpos, and flat domains of natural numbers *)
Definition natDis  : cpoType := nat_cpoType.
Definition natFlat : cppoType := PredomLift.liftCppoType natDis.

Definition natDisn n : cpoType := nprod natDis n.
Definition natFlatn n : cppoType := nprod natFlat n.

(** Any function from a discrete cpos is continuous *)
Lemma dis_all_cont (D: Type) (O : cpoType) 
      (h : discrete_cpoType D -> O) : continuous (fmonD h).
Proof.
  intro c.
  simpl.
  set (c_cte := dis_chain_cte _ c).
  assert (chain_cte _ (fmonD h << c) (h (c 0))) as L.
  unfold chain_cte in *.
  intro i. simpl.
  set (hmon := fmonD_mon h).
  unfold monotonic in hmon.
  split ;
  eapply hmon ;
  rewrite <- c_cte ;
  eauto.
  assert (Q := lub_cte_chain _ _ (h (c 0)) L).
  rewrite Q.
  unfold lub.
  simpl.
  auto.
Qed.

(** Any function from a discrete cpo is a morphism *)
Definition fcontD (D : Type) (O : cpoType) 
           (h : discrete_cpoType D -> O) : discrete_cpoType D -=> O 
  := mk_fcont (dis_all_cont _ _ h).

(** * Auxiliary results and definitions *)

(** Destruction of streams  *)
Lemma valEps_dec (D : Type) : 
   forall x : Stream D, 
     (exists x', x = Eps x') \/ (exists d, x = Val d).
Proof.
  intros x.
  destruct x.
  left.
  exists x.
  auto.
  right.
  eexists.
  eauto.
Qed.

Lemma fmono_eq (A B : ordType) (f g : A =-> B) :
  (forall x, f x =-= g x) ->
  f =-= g.
Proof.
  intro P.
  split.
  intro x.
  specialize (P x).
  rewrite P.
  auto.
  intro x.
  specialize (P x).
  rewrite <- P.
  auto.
Qed.

Lemma prod_eq (A B : ordType) (a0 a1 : A) (b0 b1 : B):
  ((a0, b0) : (A * B)%CPO) =-= (a1, b1) ->
  a0 =-= a1 /\ b0 =-= b1.
Proof.
  intro Q.
  split ;
  split ;
  eapply Q.
Qed.

Definition continuous2 {D1 D2 : cpoType} (f : ordCatType D1 D2) :=
  forall c : ordCatType natO D1,
  forall sup,
    sup =-= lub (T:=D1) c ->
    f  sup <= lub (T:=D2) (f << c).

(** Vectors to finite products *)
Fixpoint vec_to_nprod (A : cppoType) n (v : t A n) : nprod A n :=
  match v in (t _ n0) return nprod A n0 with
      nil => tt
    | a :: v' => (a, vec_to_nprod _ _ v')
  end.

(** * Generalized lifting monad and its properties *)

Section GenKleisli.
Variable P : cpoType.
Variable D : cppoType.

Fixpoint kl (f : P -> D) (x : P _BOT) (n : nat) : D :=
  match x with
      Val d => f d
    | Eps x => match n with
                   0 => PBot
                 | S n => kl f x n
               end
  end.


Lemma kl_value (f : P -> D) d n: 
  kl f (Val d) n = f d.
Proof.
  destruct n ;
  simpl ;
  auto.
Qed.

Lemma kl_strict (f : P -> D):
  forall n, kl f PBot n =-= PBot.
Proof.
  set (x := (PBot : P _BOT)).
  assert (x = Eps x) as H.
  eapply (DL_bot_eq _).
  induction n.
  simpl. auto.
  rewrite H.
  simpl.
  assumption.
Qed.

Lemma kl_inc (f : P -> D): forall x n, kl f x n <= kl f x (S n).
Proof.
  intros x n.
  generalize x.
  generalize n.
  clear x n.
  induction n.
  destruct x.
  simpl.
  eapply (leastP).
  simpl.
  eauto.
  intro x.
  destruct x.
  eapply (IHn x).
  simpl.
  eauto.
Qed.

Lemma kl_inc_more (f : P -> D): forall x n z, kl f x n <= kl f x (n + z).
Proof.
  intros x n.
  induction z.
  rewrite addn0.
  auto.
  nat_norm.
  transitivity (kl f x (n + z)).
  auto.
  eapply kl_inc.
Qed.

Lemma kl_mono (f : P -> D): forall x, monotonic (kl f x).
Proof.
  intros x n0 n1 Q.
  rewrite <- (subnKC Q).
  eapply kl_inc_more.
Qed.
  
Definition kl_chain (f : P -> D) (x : P _BOT) : natO -=> D 
  := mk_fmono (kl_mono f x).

Lemma klc_mono (f f' : P =-> D) : 
  forall x, f <= f' -> kl_chain f x <= kl_chain f' x.
Proof.
  intros x Q.
  intro n.
  generalize x.
  generalize n.
  clear x n.
  induction n.
  intros x.
  destruct x.
  simpl.
  eapply leastP.
  simpl.
  eapply Q.
  intro x.
  destruct x.
  simpl.
  eapply IHn.
  simpl.
  eapply Q.
Qed.

Lemma kl_pred (f : P -> D):
  forall k x d, pred_nth x k = Val d -> kl f x k = f d.
Proof.
  induction k.
  intros x d Q.
  unfold pred_nth in Q.
  rewrite Q.
  simpl.
  auto.
  intros x d Q.
  destruct x.
  rewrite pred_nth_Sn_acc in Q.
  simpl in Q. simpl.
  eauto.
  simpl.
  rewrite pred_nth_val in Q.
  injection Q. intros. subst.
  auto.
Qed.

Lemma kl_val (f : P -> D) : 
  forall x d, 
    x =-= Val d -> 
    exists k d',  kl f x k = f d' /\ d =-= d'.
Proof.
  intros x d Q.
  assert (L := eqValpred Q).
  destruct L as [k L']. 
  destruct L' as [d' [Q1 Q2]].
  exists k.
  exists d'.
  split ; auto.
  eapply kl_pred.
  auto.
Qed.

Lemma kl_val_eq (f : P -> D) : 
  stable f ->
  forall x d, 
    x =-= Val d -> 
    exists k,  kl f x k =-= f d.
Proof.
  intros st x d Q.
  assert (L := kl_val f x d Q).
  destruct L as [k [d' [Q1 Q2]]].
  exists k.
  rewrite Q1.
  eapply st.
  auto.
Qed.

Lemma kl_val_leq (f : P -> D) : 
  monotonic f ->
  forall x d, 
    Val d <= x -> 
    exists k, f d <= kl f x k.
Proof.
  intros mono x d Q.
  assert (Q1 := DLle_Val_exists_eq Q).
  destruct Q1 as [d' [R Q2]].
  assert (stf := monotonic_stable mono).
  assert (L := kl_val_eq f stf _ _ R).
  destruct L as [k X].
  exists k.
  rewrite X.
  eapply mono.
  auto.
Qed.

Lemma kl_incl (f : P -> D) :
  monotonic f ->
  forall x y : P _BOT, 
    x <= y -> forall n, exists m, kl f x n <= kl f y m.
Proof.
  intros mono x y Q n.
  generalize Q.
  generalize y.
  generalize x.
  generalize n.
  clear x y Q n.
  induction n.
  (* 0 *)
  intros x y Q.
  destruct x as [x | d].
  simpl.
  exists 0.
  eapply leastP.
  assert (L := kl_val_leq f mono _ _ Q).
  destruct L as [k L].
  exists k.
  simpl.
  auto.
  (* n + 1 *)
  intros x y Q.
  destruct x as [x' | d].
  assert (Q' := DLle_pred_left Q).
  simpl in Q'.
  eauto.
  assert (L := kl_val_leq f mono _ _ Q).
  destruct L as [k L].
  exists k.
  simpl.
  auto.
Qed.

Definition gkl (f : P -> D) (x : P _BOT) : D := lub (kl_chain f x).


Lemma gkl_mono (f : fmono P D) : monotonic (gkl f).
Proof.
  intros x y Q.
  unfold gkl.
  eapply lub_le_compat_weak.
  eapply kl_incl ;
  auto.
Qed.

Definition gklm (f : fmono P D) : fmono (P _BOT) D := mk_fmono (gkl_mono f).

Lemma lub_val_chain  :
  forall c : natO =-> P _BOT,
  forall d,
    lub c =-= Val d ->
    exists c',
      lub c' =-= d /\
      forall j, 
      exists i, c i =-= Val (c' j).
Proof.
  intros c d L.
  assert (H := lubval L).
  destruct H as [k [d' [Hk Q]]].
  assert (J := DLvalgetchain Hk).
  destruct J as [c' R].
  exists c'.
  split.
  assert (H := chainVallubnlub Hk 1).
  destruct H as [d1 [H C]].
  replace (DL_lubn c 1) with (lub c) in H by auto.
  assert (d =-= d1) as Q1.
  eapply vinj.
  rewrite <- L.
  assumption.
  rewrite Q1.
  rewrite C.
  eapply lub_eq_compat.
  eapply fmono_eq.
  intro n.
  symmetry.
  eapply (makechainworks Hk (R n)).
  intro j.
  exists ((k + j)%N).
  apply R.
Qed.
  
Lemma gkl_cont_value (f : P -=> D):
  forall n d c, 
    Val d =-= lub c ->
    kl f (Val d) n <= lub (gklm f << c). 
Proof.
  intros n d c Q.
  rewrite kl_value. 
  assert (lub c =-= Val d) as Q0.
  symmetry. assumption. 
  clear Q.
  assert (H := lub_val_chain _ _ Q0).
  destruct H as [c' [L R]].
  rewrite <- L.
  eapply Ole_trans.
  eapply fcontinuous.
  eapply lub_le_compat_weak.
  intros m.
  specialize (R m).
  destruct R as [i R].
  eexists i.
  simpl.
  unfold gkl.
  assert (Val (c' m) <= c i) as Q.
  rewrite <- R. auto.
  assert (J := kl_val_leq f (fmonotonic f) _ _ Q).
  destruct J as [k J].
  transitivity (kl f (c i) k).
  assumption.
  replace (kl f (c i) k) with ((kl_chain f (c i)) k) by auto.
  eapply le_lub.
Qed.

Lemma gkl_cont2 (f : P -=> D) : continuous2 (gklm f).
Proof.
  set(C := valEps_dec P).
  intros c sup Q.
  eapply lub_le.
  intro n.
  generalize Q.
  generalize sup.
  generalize n.
  clear sup Q n.
  induction n.
  (* n = 0 *)
  intros sup Q.
  destruct (C (lub c)) as [H | H].
  destruct H as [x'  Q'].
  destruct (C sup) as [R | R].
  destruct R as [p R'].
  rewrite R'.
  simpl.
  eapply leastP.
  destruct R as [d R].
  rewrite R.
  apply gkl_cont_value.
  rewrite R in Q.
  assumption.
  destruct H as [d H].
  destruct (C sup) as [R | R].
  destruct R as [x' R'].
  rewrite R'.
  simpl.
  eapply leastP.
  destruct R as [x' R].
  rewrite R.
  eapply gkl_cont_value.
  match goal with
      |- ?X => replace X with (Val x' =-= lub c) by auto
  end.
  rewrite <- R.
  assumption.
  (* n + 1 *)
  destruct (C (lub c)) as [H | H].
  destruct H as [x Q'].
  intros sup Q.
  destruct (C sup) as [R | R].
  destruct R as [x' R'].
  rewrite R'.
  simpl.
  eapply IHn.
  rewrite R' in Q.
  transitivity (Eps x').
  eapply eq_Eps.
  assumption.
  destruct R as [d R].
  rewrite R.
  eapply gkl_cont_value.
  rewrite R in Q.
  assumption.
  intros sup Q.
  destruct (C sup) as [R | R].
  destruct R as [x' R].
  rewrite R.
  simpl.
  eapply IHn.
  rewrite R in Q.
  transitivity (Eps x').
  eapply eq_Eps.
  assumption.
  destruct R as [d R].
  rewrite R.
  eapply gkl_cont_value.
  rewrite R in Q.
  assumption.
Qed.

Lemma gkl_cont (f : P -=> D) : continuous (gklm f).
Proof.
  assert (H := gkl_cont2 f).
  unfold continuous.
  unfold continuous2 in H.
  intro c.
  eapply H.
  auto.
Qed.

Definition GKL (f : P -=> D) : P _BOT -=> D := locked (mk_fcont (gkl_cont f)).

Lemma gkl_strict (f : P -=> D) : gkl f PBot =-= PBot.
Proof.
  unfold gkl.
  split.
  match goal with
      |- ?X => replace X with (lub (kl_chain f PBot) <= PBot) by auto
  end.
  eapply lub_le.
  intro n.
  eapply kl_strict.
  match goal with
      |- ?X => replace X with (PBot <= lub (kl_chain f PBot)) by auto
  end.
  eapply leastP.
Qed.

Lemma GKL_value (f : P -=> D) :
  forall x d,
    x =-= Val d ->
    GKL f x =-= f d.
Proof.
  intros x d R.
  rewrite R.
  unfold GKL.
  unlock.
  simpl.
  unfold gkl.
  eapply lub_eq_compat2.
  intro n.
  simpl.
  rewrite kl_value.
  auto.
Qed.

Lemma GKL_simpl:
  forall f x, GKL f x = gkl f x.
Proof.
  intros f x.
  unfold GKL.
  unlock.
  simpl.
  auto.
Qed.

Lemma GKL_mono : monotonic GKL.
Proof.
  intros f g Q.
  intros n.
  unfold GKL.
  unlock.
  simpl.
  unfold gkl.
  eapply lub_le_compat.
  eapply klc_mono.
  auto.
Qed.

Lemma GKL_stable : stable GKL.
Proof.
  eapply monotonic_stable.
  eapply GKL_mono.
Qed.

Definition GKLm := mk_fmono GKL_mono.

Lemma GKL_cont_value :
  forall (F : natO =-> (P -=> D)),
  forall d n,
    kl_chain (lub F) (Val d) n <= lub (GKLm << F) (Val d).
Proof.
  intros F d n.
  simpl.
  rewrite kl_value.
  eapply lub_le.
  intro i.
  transitivity (fcont_app (GKLm << F) (Val d) i).
  simpl.
  unfold GKL. unlock.
  unfold gkl.
  transitivity (kl_chain (F i) (Val d) 0).
  simpl.
  auto.
  eapply le_lub.
  eapply le_lub.
Qed.

Lemma GKL_cont : continuous GKLm.
Proof.
  unfold continuous.
  intro c.
  simpl.
  intro x.
  simpl.
  unfold gkl.
  unfold GKL. unlock.
  eapply lub_le.
  intro n.
  generalize x.
  generalize n.
  clear x n.
  induction n.
  intro x.
  destruct x as [x' | d].
  simpl.
  eapply leastP.
  eapply GKL_cont_value.
  intro x.
  destruct (valEps_dec _ x) as [H | H].
  destruct H as [x'  H].
  rewrite H.
  simpl.
  match goal with
      |- ?X => 
      replace X with (kl (lub c) x' n <= lub (GKLm << c) (Eps x')) by auto
  end.
  rewrite <- H.
  simpl in *.
  eapply Ole_trans.
  eapply IHn.
  eapply lub_le_compat.
  eapply fcont_lub_mono.
  rewrite H.
  apply (eq_Eps x').
  destruct H as [d H].
  rewrite H.
  eapply GKL_cont_value.
Qed.
  
Definition GKLc : (P -=> D) -=> (P _BOT -=> D) := mk_fcont GKL_cont.   
 
End GenKleisli.

Arguments GKL [P D] _.
Arguments GKLc [P D].
Arguments gkl  [P D] _ _.

(** Some other facts about GKL *)

Lemma GKL_respects_strictness':
  forall (P : cpoType),
  forall (D0 D1 : cppoType),
  forall (f : P -=> (D0 -=> D1)),
    (forall (x : P) (d0 : D0),  d0 =-= PBot -> f x d0 =-= PBot) ->
    forall (d : P _BOT) (d0 : D0),
      d0 =-= PBot ->
      (GKL f d) d0 <= PBot.
Proof.
  intros P D0 D1 f Q d d0 E.
  unfold GKL. unlock.
  simpl.
  eapply lub_le.
  intro n.
  destruct n.
  simpl.
  destruct d.
  simpl. auto.
  eapply Q. auto.
  simpl.
  destruct d.
  generalize n d.
  clear n d.
  induction n ;
  intro d'.
  simpl. 
  destruct d'.
  simpl. auto.
  eapply Q. auto.
  destruct d'.
  simpl.
  eauto.
  simpl.
  eapply Q.
  eapply E.
  eapply Q.
  auto.
Qed.

Lemma GKL_respects_strictness:
  forall (P : cpoType),
  forall (D0 D1 : cppoType),
  forall (f : P -=> (D0 -=> D1)),
    (forall (x : P) (d0 : D0),  d0 =-= PBot -> f x d0 =-= PBot) ->
    forall (d : P _BOT) (d0 : D0),
      d0 =-= PBot ->
      (GKL f d) d0 =-= PBot.
Proof.
  intros P D0 D1 f Q d d0 E.
  split.
  eapply GKL_respects_strictness' ;
  auto.
  eapply leastP.
Qed.
