(*begin hide*)
Require Import Utils.
Require Import Program.

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

Add LoadPath "../domain-theory".
Add LoadPath "../extended-cbn".

Require Import Lang.
Require Import Types.
Require Import DomainStuff.

Require Import OperSem.
Require Import ExSem.
Require Import InSem.

Require Import Rel.
Require Import Sets.

Require Import domoprs.
Require Import PredomAll.
Require Import PredomProd.
Require Import Domains.

Include RD.

Require Import StrictExt.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*end hide*)
(** printing ⌊ #&Escr;# *)

(** *)
(*** Chapter 4: MEANING OF TYPES
***)
(** *)

(** *Auxiliary functions *)
Definition _toIArr (θ θ' : LType)
           (f : VInf =-> SemType θ' _BOT)
           (g : SemType θ =-> VInf)
  : (DInf -=> DInf _BOT) =-> SemType (θ ⇥ θ') _BOT :=
  eta << exp_fun
      (kleisli f << KUR << ev << (Id (A:= DInf -=> DInf _BOT) >< (Roll << g))).

Definition _toEArr (θ θ' : LType)
           (f : VInf =-> SemType θ _BOT)
           (g : SemType θ' =-> VInf)
  : SemType (θ ⇥ θ') =-> (DInf -=> DInf _BOT) :=
  exp_fun (kleisli (eta << Roll << g) << ev <<
                   (KLEISLI (D0:=SemType θ) (D1:=SemType θ') >< (f << Unroll))
          ).

(** *Definition 39: Embedding-projections pairs *)
Fixpoint toI (θ : LType) : VInf =-> SemType θ _BOT :=
  match θ with
  | bool̂     => VInfToBool
  | nat̂      => VInfToNat
  | θ' ⇥ θ'' => [| [| const _ ⊥ , _toIArr (toI θ'') (toE θ') |] , const _ ⊥|]
  | θ' ⨱ θ''  => [| const _ ⊥ ,
                  uncurry (Smash _ _) << toI θ' >< toI θ'' <<
                          Unroll >< Unroll
                |] 
  end
with   toE (θ : LType) : SemType θ =-> VInf :=
match θ return SemType θ =-> VInf with
  | bool̂     => inNat << B_to_N
  | nat̂      => inNat
  | θ' ⇥ θ'' => inFun << _toEArr (toI θ') (toE θ'')
  | θ' ⨱ θ'' => inPair << Roll >< Roll << toE θ' >< toE θ''
  end
.

(** *the embeddings and the projections can be extended point-wise *)
Fixpoint GtoE (E : Env) (Γ : LCtx E) : SemCtx Γ =-> (SemEnv E) :=
  match Γ in (Vector.t _ E') return SemCtx Γ =-> SemEnv E' with
  | Vector.nil         => Id
  | Vector.cons θ _ Γ' => GtoE Γ' >< toE θ
  end.

(** *Notation *)
Notation "↓" := toE (at level 1, no associativity).
Notation "↑" := toI (at level 1, no associativity).
Notation "⇓" := GtoE (at level 1, no associativity).

(** *Auxiliary results *)
Definition toIArr (θ θ' : LType) :
  (DInf -=> DInf _BOT) -=> (SemType θ -=> SemType θ' _BOT) :=
  exp_fun (
      kleisli (↑ θ' << Unroll) << ev <<
              (Id (A:= DInf -=> DInf _BOT) >< (Roll << ↓ θ))
    ).

Definition toEArr (θ θ' : LType) :
  SemType (θ ⇥ θ') =-> (DInf -=> DInf _BOT) :=
  exp_fun (
      kleisli (eta << Roll << ↓ θ') << ev <<
              (KLEISLI (D0:=SemType θ) (D1:=SemType θ') >< (↑ θ << Unroll))
    ).

Notation "⇈" := toIArr (at level 1, no associativity).
Notation "⇊" := toEArr (at level 1, no associativity).

Lemma simplToBool_inl_inl (n : nat) :
  ↑ bool̂ (inl (inl n)) =-= N_to_B n.
Proof.
  intro n. by do 2 setoid_rewrite SUM_fun_simplx.
Qed.

Lemma simplToBool_inl_inr f : ↑ bool̂ (inl (inr f)) =-= PBot.
Proof.
  intro n ; by do 2 setoid_rewrite SUM_fun_simplx.
Qed.

Lemma simplToBool_inr p : ↑ bool̂ (inr p) =-= PBot.
Proof.
  intro n ; by setoid_rewrite SUM_fun_simplx.
Qed.

Lemma simplToNat_Nat (n : nat) : ↑ nat̂ (↑n n) =-= Val n.
Proof.
  intro n ; by do 2 setoid_rewrite SUM_fun_simplx.
Qed.

Lemma simplToNat_Arr f : ↑ nat̂ (↑f f) =-= PBot.
Proof.
  intro f ; by do 2 setoid_rewrite SUM_fun_simplx.
Qed.

Lemma simplToNat_Pair f : ↑ nat̂ (inPair f) =-= PBot.
Proof.
  intro f ; by setoid_rewrite SUM_fun_simplx.
Qed.

Lemma simplToNat_inl_inr f : ↑ nat̂ (inl (inr f)) =-= PBot.
Proof.
  intro f ; by do 2 rewrite SUM_fun_simplx.
Qed.

Lemma simplToNat_inr f : ↑ nat̂ (inr f) =-= PBot.
Proof.
  intro f ; by rewrite SUM_fun_simplx.
Qed.

Lemma simplToArr_Arr (θ θ' : LType) (f : DInf -=> DInf _BOT) :
  ↑ θ ⇥ θ' (↑f f) =-= Val (⇈ θ θ' f).
Proof.
  intros θ θ' f. simpl. do 2 rewrite SUM_fun_simplx. simpl.
  unfold KUR. apply Val_eq_compat. rewrite <- kleisli_comp2.
  reflexivity.
Qed.  

Lemma simplToArr_inl_inl (θ θ' : LType) bn : ↑ θ ⇥ θ' (inl (inl bn)) =-= PBot.
Proof.
  intros θ θ' n; by do 2 setoid_rewrite SUM_fun_simplx.
Qed.

Lemma simplToArr_Pair (θ θ' : LType) (p : DInf * DInf) :
  ↑ θ ⇥ θ' (inPair p) =-= PBot.
Proof.
  intros θ θ' p; unfold inPair; simpl; by rewrite SUM_fun_simplx. 
Qed.

Lemma simplToPair_Pair (θ θ' : LType) (p : DInf * DInf) :
  ↑ θ ⨱ θ' (inPair p) =-= (Smash _ _)
    (↑ θ (Unroll (fst p))) (↑ θ' (Unroll (snd p))).
Proof.
  intros θ θ' p. destruct p. simpl.
  rewrite SUM_fun_simplx. by simpl.
Qed.

Lemma simplToPair_inl (θ θ' : LType) d : ↑ θ ⨱ θ' (inl d) =-= PBot.
Proof.
  intros θ θ' n; by rewrite SUM_fun_simplx.
Qed.

Lemma simplToPair_Arr (θ θ' : LType) (f : DInf -=> DInf _BOT) :
  ↑ θ ⨱ θ' (↑f f) =-= PBot.
Proof.
  intros θ θ' f. simpl. by rewrite SUM_fun_simplx.
Qed.
Lemma toIValB : forall (y : VInf) (d : bool), ↑ bool̂ y =-= Val d ->
                                      y =-= inNat (B_to_N d).
Proof.
  intros y d H.
  destruct y as [[n | f] | p].
  setoid_rewrite -> simplToBool_inl_inl in H.
  destruct d. 
  simpl. destruct n. apply vinj in H. inversion H. inversion H0.
  destruct n. auto. simpl in H. elim (PBot_incon_eq (symmetry H)).
  simpl. destruct n. auto.
  destruct n. apply vinj in H. inversion H. inversion H0.
  simpl in H. elim (PBot_incon_eq (symmetry H)).
  setoid_rewrite -> simplToBool_inl_inr in H.
  elim (PBot_incon_eq (symmetry H)).
  setoid_rewrite -> simplToBool_inr in H.
  elim (PBot_incon_eq (symmetry H)).
Qed.

Lemma toIVal : forall (y : VInf) (d : nat), ↑ nat̂ y =-= Val d -> y =-= ↑n d.
Proof.
  intros y d H.
  destruct y as [[n | f] | p].
  setoid_rewrite -> simplToNat_Nat in H.
  apply (DLleVal_eq2 H).
  setoid_rewrite -> simplToNat_inl_inr in H.
  elim (PBot_incon_eq (symmetry H)).
  setoid_rewrite -> simplToNat_inr in H.
  elim (PBot_incon_eq (symmetry H)).
Qed.

Lemma toIEps : forall (y : VInf) (x : nat_cpoType _BOT),
    ↑ nat̂ y = Eps x ->  (exists g, y =-= ↑f g) \/
                        (exists p, y =-= inPair p).
Proof.
  intros y x equ.
  destruct y as [[n | h] | p].
  simpl in equ.
  unfold VInfToNat in equ.
  unfold "[| _ , _ |]" in equ.
  simpl in equ.
  unfold SUM_fun in equ.
  unfold SUM_funX in equ.
  unlock in equ.
  simpl in equ.
  discriminate equ.
  left.
    by exists h.
  right.
    by exists p.
Qed.  

Lemma toIDec (θ : LType) :
  forall (y : VInf), (exists (v : SemType θ), ↑ θ y =-= Val v) + (↑ θ y =-= ⊥).
Proof.
  intros θ y.
  dependent induction θ.
  - Case "θ = bool".
    destruct y as [[n | f] | p].
    destruct n.
    left. exists false. simpl. apply simplToBool_inl_inl.
    destruct n.
    left. exists true. simpl. apply simplToBool_inl_inl.
    right. by do 2 setoid_rewrite SUM_fun_simplx.
    right. apply simplToBool_inl_inr.
    right. apply simplToBool_inr.
  - Case "θ = nat".
    destruct y as [[n | f] | p].
    left. exists n. simpl. apply simplToNat_Nat.
    right. apply simplToNat_inl_inr.
    right. apply simplToNat_inr.
  - Case "θ = θ1 ⇥ θ2".
    destruct y as [[n | f] | p].
    right. apply simplToArr_inl_inl.
    left. eexists. apply simplToArr_Arr.
    right. apply simplToArr_Pair.
  - Case "θ = θ1 ⨱ θ2".
    destruct y as [n | p].
    right. apply simplToPair_inl.
    have sp := simplToPair_Pair θ1 θ2 p. simpl in sp.
    specialize (IHθ1 (Unroll (fst p))). destruct IHθ1 as [val1 | bot].
    specialize (IHθ2 (Unroll (snd p))). destruct IHθ2 as [val2 | bot].
    left.
    destruct val1 as [v1 eq1]. destruct val2 as [v2 eq2].
    exists (v1,v2). rewrite -> sp. rewrite -> eq1, eq2. apply SmashLemmaValVal.
    auto.
    right. rewrite -> sp. rewrite -> bot. apply SmashLemma_Bot. auto.
    right. rewrite -> sp. rewrite -> bot. apply SmashLemma_Bot. auto.
Qed.

Lemma toArrVal (θ θ' : LType) :
  (forall D (f : VInf -=> D _BOT) d, kleisli (f << ↓ θ) (↑ θ d) <= f d) ->
  (forall D (f : VInf -=> D _BOT) d, kleisli (f << ↓ θ') (↑ θ' d) <= f d) ->
  (forall x d, ↑ θ (Unroll x) =-= Val d -> Roll (↓ θ d) <= x) ->
  forall y g, ↑ (θ ⇥ θ') y =-= Val g -> exists f, y =-= ↑f f /\ ⇊ θ θ' g <= f.
Proof.
  intros θ θ' p p' s y d H.
  destruct y as [[n | g] | pa].
  simpl in H.
  unfold "[| _ , _ |]" in H.
  simpl in H.
  do 2 setoid_rewrite SUM_fun_simplx in H.
  unfold PBot in H; simpl in H; rewrite DL_bot_eq in H.
  rewrite <- DL_bot_eq in H.
  elim (DL_bot_neq (snd H)).
  exists g. split. auto. simpl in H. rewrite SUM_fun_simplx in H *.
  intro H. intro x.
  simpl. rewrite -> SUM_fun_simplx in H. simpl in H.
  pose proof (DLleVal_eq2  H) as equ.
  rewrite <- equ.
      rewrite <- comp_simpl.
      rewrite kleisli_comp.
      destruct (toIDec θ (Unroll x)) as [ val | bot].
      2 : { rewrite bot. rewrite kleisli_bot. apply DL_bot_least. }
      destruct val as [v equ'].
      assert (kleisli (g << Roll << toE θ) (toI θ (Unroll x)) <= g x).
      eapply DLle_trans.
      apply (p _ (g << Roll) (Unroll x)).
      rewrite <- comp_simpl.
      rewrite <- comp_assoc.
        rewrite RU_id.
        rewrite comp_idR.
        apply DLle_refl.
        simpl.
        rewrite comp_assoc.
        rewrite kleisli_comp.
        rewrite <- (comp_assoc (Id >< (Roll << toE θ))).
        rewrite (comp_assoc (ev << Id >< (Roll << toE θ))).
        rewrite -> (kleisli_comp _ ((eta << Roll) << toE θ')).
        rewrite (comp_assoc Unroll).
        rewrite kleisli_eta_com.
        rewrite (comp_assoc Unroll).
        assert ((kleisli ((eta << Roll) << toE θ')) << (toI θ') <= eta << Roll).
        intro x'.
        apply p'.
        assert ((kleisli ((eta << Roll) << toE θ')) << (toI θ') << Unroll <= eta).
        apply Ole_trans with (y := (eta << Roll) << Unroll).
        apply comp_le_compat. auto. auto.
        rewrite <- (comp_assoc Unroll).
        rewrite RU_id.
        by rewrite comp_idR.
        clear H0.
        rewrite equ'.
        rewrite kleisliVal.
        simpl.
        unfold id.
        rewrite (kleisli_mono H2).
        rewrite (kleisli_unit).
        simpl. unfold id.
        apply fmonotonic.
        by apply s.
  simpl in H.
  unfold "[| _ , _ |]" in H.
  simpl in H.
  rewrite SUM_fun_simplx in H *. intro H.
  unfold PBot in H; simpl in H; rewrite DL_bot_eq in H.
  rewrite <- DL_bot_eq in H. 
  elim (DL_bot_neq (snd H)).
Qed.

Lemma toArrEps (θ θ' : LType) :
  forall (y : VInf) (x : SemType θ ⇥ θ' _BOT),
    ↑ (θ ⇥ θ') y = Eps x -> (exists n, y =-= ↑n n) \/
                            (exists p, y =-= inPair p).
Proof.
  intros θ θ' y x equ.
  destruct y as [[n | g] | p].
    by left; exists n.
  simpl in equ.
  unfold "[| _ , _ |]" in equ.
  simpl in equ.
  unfold SUM_fun in equ.
  unfold SUM_funX in equ.
  unlock in equ.
  simpl in equ.
  discriminate equ.
  right; by exists p.
Qed.
  
Corollary toNatBot :
  forall (y : VInf),
    (exists (x : nat_cpoType _BOT), ↑ nat̂ y = Eps x) -> ↑ nat̂ y =-= PBot.
Proof.
  intros y [x equ].
  apply toIEps in equ as [[g equ] | [p equ]].
  rewrite equ.
    by do 2 setoid_rewrite SUM_fun_simplx.
  rewrite equ.
    by setoid_rewrite SUM_fun_simplx.
Qed.

Corollary toArrBot (θ θ' : LType) :
  forall (y : VInf),
    (exists (x : SemType θ ⇥ θ' _BOT), ↑ (θ ⇥ θ') y = Eps x) ->
    ↑ (θ ⇥ θ') y =-= PBot.
Proof.
  intros θ θ' y [x equ].
  apply toArrEps in equ as [[g equ] | [p equ]].
  rewrite equ.
  simpl. by do 2 rewrite SUM_fun_simplx.
  rewrite equ.
  simpl. by rewrite SUM_fun_simplx.
Qed.

Lemma fromToBool (b : bool_cpoType) : eta b =-= ↑ bool̂ (↓ bool̂ b).
  intro b. simpl.
  do 2 setoid_rewrite -> SUM_fun_simplx. simpl.
  destruct b. auto. auto.
Qed.

Lemma toFromBool (D : cpoType) (f : VInf -=> D _BOT) (d : VInf) :
  kleisli (f << ↓ bool̂) (↑ bool̂ d) <= f d.
Proof.
  intros D f d.
  destruct d as [[n | g] | p].
  - Case "n".
    rewrite simplToBool_inl_inl.
    destruct n. simpl. by rewrite kleisliVal.
    destruct n. simpl. by rewrite kleisliVal.
    rewrite kleisli_bot. apply DL_bot_least.
  - Case "g".
    simpl.
    rewrite simplToBool_inl_inr.
    rewrite kleisli_bot.
    apply DL_bot_least.
  - Case "p".
    rewrite simplToBool_inr.
    rewrite kleisli_bot.
    apply DL_bot_least.
Qed.

Lemma fromToNat (n : nat_cpoType) : eta n =-= ↑ nat̂ (↓ nat̂ n).
  intro n. by rewrite simplToNat_Nat.
Qed.

Lemma toFromNat (D : cpoType) (f : VInf -=> D _BOT) (d : VInf) :
  kleisli (f << ↓ nat̂) (↑ nat̂ d) <= f d
.
Proof.
  intros D f d.
  destruct d as [[n | g] | p].
  rewrite simplToNat_Nat.
  rewrite kleisliVal.
  by simpl.
  rewrite simplToNat_Arr.
  rewrite kleisli_bot.
  apply DL_bot_least.
  rewrite simplToNat_inr.
  rewrite kleisli_bot.
  apply DL_bot_least.
Qed.
  
Lemma toIProdInv (θ θ' : LType) : forall x a b,
  (↑ θ ⨱ θ') x =-= Val (a , b) ->
  exists z w , x =-= (inPair (z, w)) /\
          (Val a =-= ↑ θ (Unroll z)) /\ (Val b =-= ↑ θ' (Unroll w)).
Proof.
  intros θ θ' x a b H.
  destruct x.
  setoid_rewrite (simplToPair_inl θ θ' s) in H.
  symmetry in H.
  elim (PBot_incon_eq H).
  destruct s.
  setoid_rewrite simplToPair_Pair in H.
  simpl in H. apply SmashInv in H.
  exists s, s0. split. auto. auto.
Qed.

Lemma _EmbProjPair (θ : LType) :
  (forall (v : SemType θ), eta v =-= ↑ θ (↓ θ v))
  /\
  (forall (D : cpoType) (f : VInf -=> D _BOT) d, kleisli (f << ↓ θ) (↑ θ d) <= f d)
  /\
  (forall (d : SemType θ _BOT), d <= kleislit (↑ θ << ↓ θ) d)
  /\
  (forall (d : SemType θ _BOT), kleislit (↑ θ << ↓ θ) d <= d)
  /\
  (forall (x : DInf) (v : SemType θ), ↑ θ (Unroll x) =-= Val v -> Roll (↓ θ v) <= x).
Proof.
  dependent induction θ.
  - Case "θ = bool".
    split. apply fromToBool. split. apply toFromBool.
    split.
    cofix _EmbProjPair. destruct d.   
    rewrite kleisli_Eps. apply DLleEps. apply _EmbProjPair.
    rewrite kleisli_Val. rewrite comp_simpl. by rewrite <- fromToBool.
    split.
    cofix _EmbProjPair.
    destruct d. rewrite kleisli_Eps. apply DLleEps. apply _EmbProjPair.
    rewrite kleisli_Val. rewrite comp_simpl. by rewrite <- fromToBool.
    intros x d equ.
    apply toIValB in equ. rewrite <- RUid with (x:=x).
    simpl. by rewrite -> equ.
  - Case "θ = nat".
    split. apply fromToNat. split. apply toFromNat.
    split.
    cofix _EmbProjPair. destruct d.   
    rewrite kleisli_Eps. apply DLleEps. apply _EmbProjPair.
    rewrite kleisli_Val. rewrite comp_simpl. by rewrite <- fromToNat.
    split.
    cofix _EmbProjPair.
    destruct d. rewrite kleisli_Eps. apply DLleEps. apply _EmbProjPair.
    rewrite kleisli_Val. rewrite comp_simpl. by rewrite <- fromToNat.
    intros x d equ.
    apply toIVal in equ.
    simpl. rewrite <- equ. rewrite <- comp_simpl. by rewrite RU_id.
  - Case "θ = θ1 ⇥ θ2".
    destruct IHθ1 as [fromTo1 [toFrom1 [lt1 [gt1 p1]]]].
    destruct IHθ2 as [fromTo2 [toFrom2 [lt2 [gt2 p2]]]].
    split.
    + SCase "fromTo = Id".
      intro f. rewrite simplToArr_Arr; fold toI toE.
      apply Val_stable. apply fmon_eq_intro.
      intro v. simpl.
      setoid_replace (Unroll (Roll (toE θ1 v))) with (toE θ1 v)
        by (rewrite <- comp_simpl; by rewrite UR_id).
      rewrite <- fromTo1.
      rewrite kleisliVal.
      do 2 rewrite <- comp_simpl.
      rewrite <- (comp_assoc _ Roll eta).
      rewrite <- kleisli_comp2; rewrite <- comp_assoc.
      rewrite (comp_assoc (toE θ2)  Roll Unroll).
      rewrite UR_id; rewrite comp_idL. simpl.
      rewrite -> kleisli_simpl. apply (Ole_antisym (lt2 (f v)) (gt2 (f v))).
      split.
    + SCase "fromTo <= Id".
      intros D F d. destruct d as [[n | f] | p].
      rewrite simplToArr_inl_inl. rewrite kleisli_bot. apply DL_bot_least.
      rewrite simplToArr_Arr.
      rewrite kleisliVal.
      simpl. apply fmonotonic.
      intro x. simpl.
      rewrite <- comp_simpl; rewrite kleisli_comp.
      destruct (toIDec θ1 (Unroll x)) as [val | bot].
      2 : { rewrite bot. rewrite kleisli_bot. apply DL_bot_least. }
      destruct val as [v equ].
      assert (kleisli (f << Roll << toE θ1) (toI θ1 (Unroll x)) <= f x).
      eapply DLle_trans.
      apply (toFrom1 _ (f << Roll) (Unroll x)).
      rewrite <- comp_simpl; rewrite <- comp_assoc; rewrite RU_id;
        rewrite comp_idR. apply DLle_refl.
      rewrite comp_assoc.
      rewrite <- (comp_assoc (Id >< (Roll << toE θ1))).
      rewrite (comp_assoc (ev << Id >< (Roll << toE θ1))).
      rewrite -> (kleisli_comp _ ((eta << Roll) << toE θ2)).
      rewrite (comp_assoc Unroll).
      assert ((kleisli ((eta << Roll) << toE θ2)) << (toI θ2) <= eta << Roll).
      intro x'.
      apply toFrom2.
      assert ((kleisli ((eta << Roll) << toE θ2)) << (toI θ2) << Unroll <= eta).
      apply Ole_trans with (y := (eta << Roll) << Unroll).
      apply comp_le_compat. auto. auto.
      rewrite <- comp_assoc. rewrite RU_id. by rewrite comp_idR. clear H0.
      rewrite equ.
      rewrite kleisliVal.
      simpl; unfold id.
      rewrite (kleisli_mono H1).
      rewrite (kleisli_unit).
      simpl; unfold id.
      apply fmonotonic. by apply p1.
      rewrite simplToArr_Pair. rewrite kleisli_bot. apply DL_bot_least.
      split.
    + SCase "id <= kleisli fromTo".
      cofix _EmbProjPair.
      destruct d as [y | f].
      rewrite kleisli_Eps. apply DLleEps. apply _EmbProjPair.
      rewrite kleisli_Val.
      simpl.
      rewrite SUM_fun_simplx.
      unfold _toIArr.
      simpl. rewrite SUM_fun_simplx.
      apply Val_le_compat.
      apply fmon_eq_intro.
      intro v; simpl.
      setoid_replace (Unroll (Roll (toE θ1 v))) with (toE θ1 v)
        by (rewrite <- comp_simpl; rewrite UR_id).
      rewrite <- fromTo1.
      rewrite kleisliVal.
      do 2 rewrite <- comp_simpl.
      unfold KUR.
      rewrite <- kleisli_comp2; rewrite <- comp_assoc.
      rewrite <- kleisli_comp2; rewrite <- comp_assoc.
      rewrite (comp_assoc (toE θ2)  Roll Unroll).
      rewrite UR_id.
      rewrite comp_idL.
      split. hnf. rewrite kleisli_simpl. apply (gt2 (f v)).
      hnf. rewrite kleisli_simpl. apply (lt2 (f v)).
        by unfold id.
    split.
    + SCase "kleislit fromTo <= id".
      cofix _EmbProjPair.
      destruct d as [y | f].
      rewrite kleisli_Eps. apply DLleEps. apply _EmbProjPair.
      rewrite kleisli_Val.
      simpl.
      rewrite SUM_fun_simplx.
      unfold _toIArr.
      simpl. rewrite SUM_fun_simplx.
      apply Val_le_compat.
      intro x; simpl.
      setoid_replace (Unroll (Roll (toE θ1 x))) with (toE θ1 x)
        by (rewrite <- comp_simpl; rewrite UR_id).
      rewrite <- fromTo1.
      rewrite kleisliVal.
      do 2 rewrite <- comp_simpl. unfold KUR.
      rewrite <- kleisli_comp2; rewrite <- comp_assoc.
      rewrite <- kleisli_comp2; rewrite <- comp_assoc.
      rewrite (comp_assoc (toE θ2)  Roll Unroll).
      rewrite UR_id; rewrite comp_idL.
      hnf. rewrite kleisli_simpl. apply (gt2 (f x)). by unfold id.
    + SCase "last case".
      intros x g equ.
      destruct (toArrVal toFrom1 toFrom2 p1 equ) as [h [equ' lt]] .
      setoid_replace x with (Roll (Unroll x)).
      rewrite equ'.
      apply fmonotonic.
      apply lt.
      rewrite <- comp_simpl.
        by rewrite RU_id.
  - Case "θ = θ1 ⨱ θ2".
    destruct IHθ1 as [fromTo1 [toFrom1 [lt1 [gt1 p1]]]].
    destruct IHθ2 as [fromTo2 [toFrom2 [lt2 [gt2 p2]]]].
    split.
    + SCase "fromTo = Id".
      intros (v1,v2). simpl; setoid_rewrite -> SUM_fun_simplx.
      simpl. do 2 rewrite -> URid. rewrite <- fromTo1, <- fromTo2.
      symmetry. apply SmashLemmaValVal. auto.
    split.
    + SCase "fromTo <= Id".
      intros D F d. destruct d as [[n | f] | p].
      rewrite simplToPair_inl. rewrite kleisli_bot. apply DL_bot_least.
      rewrite simplToPair_inl. rewrite kleisli_bot. apply DL_bot_least.
      rewrite simplToPair_Pair. simpl.
      have toI_fstp := toIDec θ1 (Unroll (fst p)).
      have toI_sndp := toIDec θ2 (Unroll (snd p)).
      destruct toI_fstp as [valf | bot].
      destruct toI_sndp as [vals | bot].
      destruct valf. destruct vals. rewrite -> H, -> H0.
      rewrite -> Smash_ValVal. rewrite -> kleisliVal. simpl.
      have pair_c := pair_le_compat (p1 (fst p) x H) (p2 (snd p) x0 H0).
      have in2_c := fmon_le_compat
                     (x:=in2 (A:=nat_cpoType) << in2) (y:=in2 << in2) _ pair_c.
      eapply Ole_trans.
      apply fmon_le_compat. reflexivity. 
      apply in2_c. reflexivity. clear pair_c in2_c.
      simpl. by rewrite <- surjective_pairing.
      rewrite -> (SmashLemma_Bot (or_intror bot)).
      rewrite -> kleisli_bot. apply leastP.
      rewrite -> (SmashLemma_Bot (or_introl bot)).
      rewrite -> kleisli_bot. apply leastP.
    split.
    + SCase "id <= kleisli fromTo".
      cofix _EmbProjPair.
      intros d. destruct d as [y | [a b]].
      rewrite kleisli_Eps. apply DLleEps. apply _EmbProjPair.
      rewrite kleisli_Val. simpl. rewrite SUM_fun_simplx.
      simpl. do 2 rewrite -> URid. rewrite <- fromTo1, <- fromTo2. simpl.
        by rewrite -> Smash_ValVal.
    split.
    + SCase "kleislit fromTo <= id".
      cofix _EmbProjPair.
      intros d. destruct d as [y | [a b]].
      rewrite kleisli_Eps. apply DLleEps. apply _EmbProjPair.
      rewrite kleisli_Val. simpl. rewrite SUM_fun_simplx.
      simpl. do 2 rewrite -> URid. rewrite <- fromTo1, <- fromTo2. simpl.
        by rewrite -> Smash_ValVal.
    + SCase "last case".
      intros x (a, b) equ.
      apply toIProdInv in equ. destruct equ as [a' [b' [? [? ?]]]].
      setoid_replace x with (Roll (Unroll x)).
      apply fmonotonic. rewrite -> H. simpl.
      have in2_c := fmon_le_compat
                     (x:=in2 (A:=nat_cpoType) << in2) (y:=in2 << in2) _.
      apply in2_c. reflexivity. clear in2_c.
      apply pair_le_compat. apply p1. auto. apply p2. auto.
        by rewrite RUid.
Qed.

Corollary EmbProjPair θ :
       (forall v : SemType θ, ↑⊥v =-= (↑θ) (↓θ v)) /\
       (forall (d : VInf), (kleisli (eta << ↓ θ)) (↑θ d) <= eta d).
Proof.
  intro θ. destruct (_EmbProjPair θ) as [pr [em [_ [_ _]]]].
  split.
  apply pr. apply (em _ eta).
Qed.
