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
Require Import Biorthogonality.
Require Import StepIndexing.
Require Import Sets.

Require Import domoprs.
Require Import PredomAll.
Require Import Domains.

Require Import Min NPeano.

Require Import Relations.Relation_Operators.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.

Notation "x ∉ X" := (~ (In _ X x)) (at level 1, no associativity).
Notation "x ∈ X" := (In _ X x) (at level 1, no associativity).
(*end hide*)
(** *)
(*** Chapter 4: ADEQUACY ***)
(** *)

(** *Observation *)
Definition Antiexec_step (R : iRel (Expr 0) FS) : Prop :=
  forall (e e' : Expr 0) (E E' : FS) (i : nat),
    R i e E -> ((E', e') ⟼ (E, e)) -> R (i.+1) e' E'
.

Record RelE := mkrel {
       rel       :> iRel (Expr 0) FS;
       stepI     :> StepI (irel_reli rel);
       anti_step :> Antiexec_step rel
}.

Section OperApprox.

Variable RE : RelE.

Import Relations.Relation_Operators.
  
(** Denotational approximation *)

Definition DownR : iRel (Expr 0) FS -> iRel (V 0) FS :=
  fun R n v E => R n (VAL v) E.
Notation "'↓r' X" := (DownR X) (at level 1, no associativity).
Notation "↓ X" := (bbot (mrel (↓r RE)) X) (at level 1, no associativity).
Notation "⇑ X" := (btop (mrel RE) X) (at level 1, no associativity).

(** *Definition 26: Lifted extension *)
Definition Ω (dv : VInf _BOT)  (DR : nat -> V 0 -> VInf -> Prop) :
  Power_set (Indexed (V 0)) :=
  fun (iv : nat * V 0) =>
    let (i,v) := iv in exists (d : VInf), dv =-= eta d /\ DR i v d
.

(** *Definition 50: Operational approximation for values *)
Fixpoint OperApproxV (θ : LType) (n : nat) : V 0 -> VInf -> Prop :=
  match θ as θ return V 0 -> VInf -> Prop with
  | bool̂     => fun v dv => exists (b : bool), dv =-= inNat (B_to_N b) /\ v = BOOL b
  | nat̂     => fun v dv => (exists (m : nat), dv =-= inNat m /\ v = NAT m) \/
                          (exists (b : bool), dv =-= inNat (B_to_N b) /\ v = BOOL b)
  | θ ⇥ θ' =>
    let OperApproxE (θ : LType) (n : nat) : Expr 0 -> VInf _BOT -> Prop :=
        fun e de  => (n,e) ∈ ⇑ ↓ (Ω de (@OperApproxV θ))
    in fun v df  => exists e, v = FUN e /\
                  exists (f : DInf -=> DInf _BOT), df =-= inFun f /\
                  forall (n' : nat) (w : V 0) (dw : VInf),
                    (n' < n)%coq_nat ->
                    @OperApproxV θ  n' w dw ->
                    @OperApproxE θ' n' (e⎩[w,(λ e)]⎭) (KUR (f (Roll dw)))
  | θ ⨱ θ' => fun v vv => exists v1 v2, v = VPAIR v1 v2 /\
                        exists (dv1 dv2 : DInf), vv =-= inPair (dv1, dv2) /\
                        forall (n' : nat),
                          (n' < n)%coq_nat ->
                          @OperApproxV θ  n' v1 (Unroll dv1) /\
                          @OperApproxV θ' n' v2 (Unroll dv2)
  end
.

(** *Definition 49: Operational approximation for expressions *)
Definition OperApproxE (θ : LType) (n : nat) : Expr 0 -> VInf _BOT -> Prop :=
  fun e de  => (n,e) ∈ ⇑ ↓ (Ω de (@OperApproxV θ)).

(** *Notation *)
Notation "v ◁ i | dv ⦂ θ" := (@OperApproxV θ i v dv)
                             (at level 1, no associativity).
Notation "e ◀ i | de ⦂ θ" := (@OperApproxE θ i e de)
                             (at level 1, no associativity).

Lemma OAV_StepI : forall (θ : LType) (v : V 0) (dv : VInf) (i : nat),
    (v ◁i.+1| dv ⦂ θ) -> (v ◁i| dv ⦂ θ).
Proof.
  intros θ v dv i H.
  induction θ.
  - Case "θ = bool".
    simpl in *.
    destruct H as [b [? ?]].
    exists b. auto.
  - Case "θ = nat".
    simpl in *.
    destruct H as [[j [? ?]] | [j [? ?]]].
    left. exists j. auto.
    right. exists j. auto.
  - Case "θ = θ1 ⇥ θ2".
    simpl in *.
    destruct H as [e [? [f [? ?]]]].
    exists e. split. apply H.
    exists f. split. apply H0.
    intros j w dw H2 H3.
    apply H1.
    apply Lt.lt_S. apply H2.
    apply H3.
  - Case "θ = θ1 ⨱ θ2".
    simpl in *.
    destruct H as [v1 [v2 [eq [dv1 [dv2 [? ?]]]]]].
    exists v1, v2. split. auto. exists dv1, dv2. split. auto.
    intros j H1.
    apply H0.
    apply Lt.lt_S. auto.
Qed.

Lemma OAE_StepI : forall (θ : LType) (e : Expr 0) (de : VInf _BOT) (i : nat),
    (e ◀i.+1| de ⦂ θ) -> (e ◀i| de ⦂ θ).
Proof.
  intros θ e de i H.
  intros jfs jfs_in.
  specialize (H jfs jfs_in).
  destruct jfs as [j fs].
  simpl.
  have H0 := Min.min_spec i j.
  destruct H0. destruct H0 as [? ?].
  rewrite -> H1. unfold mrel in H.
  apply Lt.lt_le_S in H0.
  apply Min.min_l in H0. rewrite -> H0 in H.
  apply rel_equiv.
  apply (decreasing (stepI RE) i).
  apply H.
  destruct H0 as [? ?].
  rewrite -> H1. unfold mrel in H.
  rewrite <- H1 in H. rewrite -> NPeano.Nat.min_assoc in H.
  rewrite (Min.min_r (i.+1) i (Le.le_n_Sn i)) in H.
  rewrite H1 in H. apply H.
Qed.

(** *Lemma : Operational approximations are Step-Indexed *)
Lemma OAV_Gen_StepI : forall (θ : LType) (v : V 0) (dv : VInf) (i j : nat),
    (j <= i)%coq_nat -> (v ◁i| dv ⦂ θ) -> (v ◁j| dv ⦂ θ).
Proof.
  intros θ v dv i j j_le_i v_A_dv.
  induction i.
  inversion j_le_i. apply v_A_dv.
  apply NPeano.Nat.le_succ_r in j_le_i.
  destruct j_le_i.
  rename H into j_le_i.
  apply IHi.
  apply j_le_i. apply OAV_StepI in v_A_dv. apply v_A_dv.
  rename H into j_e_i.
  rewrite j_e_i. apply v_A_dv.
Qed.

(** *Lemma : Operational approximations are Step-Indexed *)
Lemma OAE_Gen_StepI : forall (θ : LType) (e : Expr 0) (de : VInf _BOT) (i j : nat),
    (j <= i)%coq_nat -> (e ◀i| de ⦂ θ) -> (e ◀j| de ⦂ θ).
Proof.
  intros θ e de i j j_le_i e_A_de.
  induction i.
  inversion j_le_i. apply e_A_de.
  apply NPeano.Nat.le_succ_r in j_le_i.
  destruct j_le_i.
  rename H into j_le_i.
  apply IHi.
  apply j_le_i. apply OAE_StepI in e_A_de. apply e_A_de.
  rename H into j_e_i.
  rewrite j_e_i. apply e_A_de.
Qed.

(** *Definition : Operation approximation for contexts *)
Definition OperApproxCtx (E : Env) (Γ : LCtx E)
  : nat -> (Sub E 0) -> SemEnv E -> Prop :=
  fun i σ η => forall (v : Var E), ((v⎨ v ⎬⎧ σ ⎫) ◁i| (SemVar v η) ⦂ (lookupType Γ v))
.

(** *Notation *)
Notation "σ ⊴ i | η ⦂ Γ" := (@OperApproxCtx _ Γ i σ η)
                             (at level 1, no associativity).

Lemma OAC_StepI : forall (E : Env) (Γ : LCtx E)
                    (σ : Sub E 0) (η : SemEnv E) (i : nat),
    (σ ⊴i.+1| η ⦂ Γ) -> (σ ⊴i| η ⦂ Γ).
Proof.
  intros E Γ σ η i H.
  intro v.
  specialize (H v).
  apply OAV_StepI. apply H.  
Qed.

Lemma OAC_Gen_StepI : forall (E : Env) (Γ : LCtx E)
                    (σ : Sub E 0) (η : SemEnv E) (i j : nat),
    (j <= i)%coq_nat -> (σ ⊴i| η ⦂ Γ) -> (σ ⊴j| η ⦂ Γ).
Proof.
  intros E Γ σ η i j j_le_i σ_A_η.
  intro v.
  specialize (σ_A_η v).
  eapply OAV_Gen_StepI.
  apply j_le_i.
  apply σ_A_η.
Qed.

(** *Definition : Approximations of open expressions *)
Definition GenOperApproxV
           (E : Env) (Γ : LCtx E) (θ : LType) :
  (V E) -> (SemEnv E =-> VInf) -> Prop :=
  fun v dv => forall i σ η, (σ ⊴i| η ⦂ Γ) -> (v ⎧ σ ⎫ ◁i| dv η ⦂ θ).

Definition GenOperApproxE
           (E : Env) (Γ : LCtx E) (θ : LType) :
  (Expr E) -> (SemEnv E =-> VInf _BOT) -> Prop :=
  fun e f  => forall i σ η, (σ ⊴i| η ⦂ Γ) -> (e ⎩ σ ⎭ ◀i| f η ⦂ θ).

(** *Notation *)
Notation "Γ 'v⊢' v ◁̂ dv ⦂ θ" := (@GenOperApproxV _ Γ θ v dv)
                                     (at level 201, no associativity).

Notation "Γ 'e⊢' e ◀̂ de ⦂ θ" := (@GenOperApproxE _ Γ θ e de)
                                     (at level 201, no associativity).

Lemma Case1 : forall (E : Env) (Γ : LCtx E) (v : Var E),
    (Γ v⊢ (v⎨ v ⎬) ◁̂ (SemVar v) ⦂ (lookupType Γ v)).
Proof.
  intros E Γ v.
  intros i σ η σ_A_η.
  apply (σ_A_η v).
Qed.

Lemma RE_eq_Fullset : forall (e : Expr 0) (fs : FS), (rel RE) 0 e fs.
Proof.
  intros e fs.
  apply rel_equiv.
  apply (zero (stepI RE)).
  apply Full_intro.
Qed.

Lemma OAE_Z_Fullset : forall (θ : LType) (e : Expr 0) (d : VInf _BOT), e ◀ 0 | d ⦂ θ.
Proof.
  intros θ e d ifs ifs_in. destruct ifs as [i fs]. simpl. apply RE_eq_Fullset.
Qed.

Lemma Expand2ApproxCtx :
  forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
    (σ : Sub E 0) (η : SemEnv E)
    (v v' : V 0) (dv dv' : VInf) (i : nat),
    σ ⊴i| η ⦂ Γ -> OperApproxV θ i v dv -> OperApproxV θ' i v' dv' ->
    (composeSub [v', v] (liftSub (liftSub σ))) ⊴i| (η, dv,dv') ⦂ (θ' × θ × Γ).
Proof.
  intros θ θ' E Γ σ η v v' dv dv' i H H0 H1.
  intros x.
  dependent destruction x.
  - Case "x = ZVAR".
    unfold "_ ⎧ _ ⎫".
    rewrite mapVAR. unfold lookupV. simpl. unfold composeSub.
    unfold "_ ⎧ _ ⎫".
    rewrite mapVAR. simpl.
    apply H1.
  - Case "x = SVAR".
    generalize dependent x.
    dependent destruction x.
    + SCase "x = SVAR ZVAR".
      unfold lookupV. simpl.
      unfold "_ ⎧ _ ⎫".
      rewrite mapVAR. simpl vl.
      unfold composeSub.
      unfold "_ ⎧ _ ⎫".
      rewrite mapVAR.  simpl vl.
      apply H0.
    + SCase "x = SVAR SVAR".
      simpl.
      rewrite (fst (substComposeSub _)).
      unfold "_ ⎧ _ ⎫".
      rewrite mapVAR. simpl vl.
      do 2 rewrite <-(fst (applyComposeRen _)).
      unfold composeRen.
      simpl. unfold idSub.
      rewrite -> (fst (applyIdMap _ _)).
      specialize (H x).
      apply H.
Qed.

Lemma FIXP_Step : forall (E : Env)
                (η : SemEnv E)
                (de : SemEnv E.+2 =-> VInf _BOT) (dw : VInf),
    KUR ((FIXP ((F de) η)) (Roll dw))
    =-=
    de (η, ((inFun << FIXP) << F de) η, dw).
Proof.
  intros E η de dw.
  rewrite FIXP_eq.
  unfold KUR.
  simpl.
  unfold id.
  assert (Unroll (Roll dw) =-= dw).
  - Case "Assert".
    rewrite <- comp_simpl.
    rewrite UR_id. auto.
  assert (forall f, (kleisli (eta << DomainStuff.Unroll))
                   ((kleisli (eta << ExSem.Roll)) f) =-= f).
  - Case "Assert".
    intros f.
    rewrite <- comp_simpl.
    rewrite <- kleisli_comp2.
    rewrite <- comp_assoc.
    rewrite UR_id. rewrite comp_idR.
    by rewrite kleisli_unit.
  rewrite H.    
  by apply H0.
Qed.

Lemma Omega_compat : forall (θ : LType) (iv : Indexed (V 0)) (d d' : VInf _BOT),
    d =-= d' ->
    iv ∈ (Ω d (OperApproxV θ)) -> iv ∈ (Ω d' (OperApproxV θ)).
Proof.
  intros θ iv d d' d_eq_d' iv_in.
  destruct iv as [i v].
  destruct iv_in as [d'' [? ?]].
  exists d''. split. rewrite <- d_eq_d'. apply H.
  apply H0.
Qed.

Lemma FS_In_compat : forall (θ : LType) (ifs : Indexed FS) (d d' : VInf _BOT),
    d =-= d' ->
    ifs ∈ (bbot (mrel ↓r RE) (Ω d (OperApproxV θ))) ->
    ifs ∈ (bbot (mrel ↓r RE) (Ω d' (OperApproxV θ))).
Proof.
  intros θ ifs d d' d_eq_d' ifs_in.
  intros iv iv_in.
  apply ifs_in.
  apply Omega_compat with (d:=d').
  apply tset_sym. apply d_eq_d'.
  apply iv_in.
Qed.

Lemma OAE_compat : forall (θ : LType) (e : Expr 0) (d d' : VInf _BOT) (i : nat),
    d =-= d' -> (e ◀i| d ⦂ θ) -> (e ◀i| d' ⦂ θ).
Proof.
  intros θ e d d' i d_eq_d' e_A_d.
  intros ifs ifs_in.
  apply e_A_d.
  eapply FS_In_compat. apply tset_sym. apply d_eq_d'.
  apply ifs_in.
Qed.

Lemma OAV_compat : forall (θ : LType) (v : V 0) (d d' : VInf) (i : nat),
    d =-= d' -> (v ◁i| d ⦂ θ) -> (v ◁i| d' ⦂ θ).
Proof.
  intros θ v d d' i d_eq_d' v_A_d.
  dependent destruction θ.
  destruct v_A_d. exists x. by rewrite <- d_eq_d'.
  destruct v_A_d as [[n [? ?]] | [b [? ?]]].
  left. exists n. by rewrite <- d_eq_d'.
  right. exists b. by rewrite <- d_eq_d'.
  destruct v_A_d as [f [feq [df [? ?]]]].
  exists f. split. auto. exists df. split. rewrite <- d_eq_d'. auto. auto.
  destruct v_A_d as [v1 [v2 [eq [dv1 [dv2 [? ?]]]]]].
  exists v1, v2. split. auto. exists dv1, dv2. split. rewrite <- d_eq_d'. auto.
  auto.
Qed.

Lemma Case2 : forall (E : Env) (θ θ' : LType) (Γ : LCtx E)
                (e : Expr E.+2) (de : SemEnv E.+2 =-> VInf _BOT),
    ((θ'×(θ' ⇥ θ)×Γ) e⊢ e ◀̂ de ⦂ θ) ->
    (Γ v⊢ (FUN e) ◁̂ (inFun << FIXP << F de) ⦂ θ' ⇥ θ).
Proof.
  intros E θ θ' Γ e de e_A_de.
  intro i. induction i.
  - Case "i = 0".
    intros σ η σ_A_η.
    exists (e ⎩liftSub (liftSub σ)⎭). split. auto.
    exists (FIXP ((F de) η)). split. auto.
    intros k w dw k_le_j w_A_dw.
    inversion k_le_j.
  - Case "i => i+1".
    intros σ η σ_A_η.
    exists (e ⎩liftSub (liftSub σ)⎭). split. auto.
    exists (FIXP ((F de) η)). split. auto.
    intros k w dw k_le_i w_A_dw.
    apply Lt.lt_n_Sm_le in k_le_i. inversion k_le_i.
    rewrite <- (snd (substComposeSub _)).
    eapply OAE_compat. symmetry. apply FIXP_Step.
    eapply e_A_de.
    apply Expand2ApproxCtx.
    apply OAC_StepI in σ_A_η. apply σ_A_η.
    apply IHi. apply OAC_StepI in σ_A_η. apply σ_A_η.
    rewrite <- H. apply w_A_dw.
    rewrite <- (snd (substComposeSub _)).
    eapply OAE_compat. symmetry. apply FIXP_Step.
    eapply e_A_de.
    apply Expand2ApproxCtx.
    apply OAC_Gen_StepI with (j:=k) in σ_A_η. apply σ_A_η.
    auto.
    apply OAC_StepI in σ_A_η.
    specialize (IHi _ _ σ_A_η).
    apply OAV_Gen_StepI with (j:=k) in IHi.
    apply IHi. apply k_le_i.
    apply w_A_dw.
Qed.    

Lemma Case3 : forall (θ : LType) (E : Env) (Γ : LCtx E)
                (v : V E)
                (dv : SemEnv E =-> VInf),
    (Γ v⊢ v ◁̂ dv ⦂ θ) -> (Γ e⊢ (VAL v) ◀̂ (eta << dv) ⦂ θ).
Proof.
  intros θ E Γ v dv v_A_dv.
  intros i σ η σ_A_η.
  simpl.
  unfold "_ ⎩ _ ⎭"; rewrite mapVAL; fold v ⎧ σ ⎫.
  intros ifs ifs_in.
  specialize (ifs_in (i,v ⎧ σ ⎫)). simpl in ifs_in.
  apply ifs_in. exists (dv η). split. auto.
  apply v_A_dv. apply σ_A_η.
Qed.

Lemma RelE_down_closed : forall (e : Expr 0) (fs : FS) (i j : nat),
    (j <= i)%coq_nat -> (rel RE) i e fs -> (rel RE) j e fs.
Proof.
  intros e fs i.
  induction i.
  - Case "i = 0".
    intros j j_le_i e_Ri_fs.
    inversion j_le_i.
    apply e_Ri_fs.
  - Case "i => i+1".
    intros j j_le_i e_Ri_fs.
    apply Lt.le_lt_or_eq in j_le_i.
    destruct j_le_i.
    apply Lt.lt_le_S in H.
    apply Le.le_S_n in H.
    apply IHi. apply H.
    apply (fst (rel_equiv _ _ _ _)) in e_Ri_fs.
    apply (decreasing (stepI RE) _) in e_Ri_fs.
    apply (snd (rel_equiv _ _ _ _)) in e_Ri_fs.
    apply e_Ri_fs.
    rewrite H.
    apply e_Ri_fs.
Qed.

Lemma Ω_down_closed : forall (θ : LType) (d : VInf _BOT) (v : V 0) (i j : nat),
    (i, v) ∈ (Ω d (OperApproxV θ)) ->
    (j <= i)%coq_nat ->
    (j, v) ∈ (Ω d (OperApproxV θ)).
Proof.
  intros θ d.
  intros v i j iv_in j_le_i.
  destruct iv_in as [d' [? ?]].
  exists d'. split. apply H.
  apply OAV_Gen_StepI with (i:=i).
  apply j_le_i.
  apply H0.
Qed.

Lemma bbot_down_closed : forall (θ : LType) (d : VInf _BOT) (fs : FS) (i j : nat),
    (i, fs) ∈ (bbot (mrel ↓r RE) (Ω d (OperApproxV θ))) ->
    (j <= i)%coq_nat ->
    (j, fs) ∈ (bbot (mrel ↓r RE) (Ω d (OperApproxV θ))).
Proof.
  intros θ d fs i j H j_le_i.
  intros iv iv_in.
  destruct iv as [i' v].
  specialize (H (i',v) iv_in).
  unfold "↓r", mrel in *.
  apply NPeano.Nat.min_le_compat_l with (p:=i') in j_le_i.
  eapply RelE_down_closed.
  apply j_le_i.
  apply H.
Qed.  
 
Lemma Case4 :
  forall (E : Env) (Γ : LCtx E) (op : OrdOp) (e e': Expr E)
    (d d' : SemEnv E =-> VInf _BOT),
    (Γ e⊢ e ◀̂ d ⦂ nat̂) -> (Γ e⊢ e' ◀̂ d' ⦂ nat̂) ->
    (Γ e⊢ (OOp op e e') ◀̂ (GenOrdOp (SemOrdOp op) d d') ⦂ bool̂).
Proof.
  intros E Γ op e e' d d' e_A_d e'_A_d'.
  intros i σ η σ_A_η. unfold "_ ◀ _ | _ ⦂ _". unfold btop. unfold bbot.
  eapply btop_weakened.
  - Case "Down Closed".
    intros fs m n H n_le_m. eapply bbot_down_closed. apply H. apply n_le_m.
  - Case "Proof".
    intros ifs ifs_in.
    unfold "_ ⎩ _ ⎭"; rewrite mapOOp; fold e ⎩ σ ⎭ ; fold e' ⎩ σ ⎭.
    destruct ifs as [i' fs].
    intros i'_le_i.
    destruct i'.
    apply RE_eq_Fullset.
    eapply anti_step. 2 : { apply SOOp. }
    apply (OAC_Gen_StepI i'_le_i) in σ_A_η.
    apply OAC_StepI in σ_A_η.
    specialize (e_A_d i' σ η σ_A_η).
    specialize (e_A_d (i'.+1, PUSHLOOp op fs (e' ⎩ σ ⎭))).
    unfold mrel at 2 in e_A_d.
    rewrite (Min.min_l _ _ (Le.le_n_Sn i')) in e_A_d.
    apply e_A_d.
    eapply bbot_weakened.
    + SCase "Down Closed".
      intros v m n v_in n_le_m. eapply Ω_down_closed. apply v_in. apply n_le_m.
    + SCase "Proof".
      intros iv iv_in.
      destruct iv as [iv v].
      intro iv_le_i'. unfold "↓r".
      destruct iv. apply RE_eq_Fullset.
      destruct iv_in as [? [? [[xv [? ?]] | [xv [? ?]]]]].
      rewrite H1.
      eapply anti_step. 2 : { apply IOOp. }
      apply (OAC_Gen_StepI (Le.le_S_n _ _ iv_le_i')) in σ_A_η.
      specialize (e'_A_d' iv σ η σ_A_η).
      specialize (e'_A_d' (iv.+1, PUSHROOp op fs ⌊xv⌋)).
      unfold mrel at 2 in e'_A_d'.
      rewrite (Min.min_l _ _ (Le.le_n_Sn iv)) in e'_A_d'.
      apply e'_A_d'.
      eapply bbot_weakened.
      * SSCase "Down Closed".
        intros w m n w_in n_le_m. eapply Ω_down_closed. apply w_in. apply n_le_m.
      * SSCase "Proof".
        intros iv' iv'_in. unfold "↓r".
        destruct iv' as [iv' v']. intro iv'_le_iv.
        destruct iv'. apply RE_eq_Fullset.
        destruct iv'_in as [? [? [[xv' [? ?]] | [xv' [? ?]]]]].
        ** SSSCase "iv = Nat ∧ iv' = Nat".
           rewrite H4.
           eapply anti_step.
           2 : { apply DOOp. }
           specialize (ifs_in (iv', BOOL (SemOrdOp op xv xv'))).
           unfold mrel, "↓r" in ifs_in.
           rewrite Min.min_l in ifs_in.
           2 : { apply Le.le_trans with (m:=iv.+1).
                 apply Le.le_trans with (m:=iv'.+1).
                 apply Le.le_n_Sn. auto. apply iv_le_i'.
           }
           apply ifs_in.
           unfold "∈", Ω. simpl.
           exists (inNat (B_to_N (SemOrdOp op xv xv'))).
           split. simpl.
           rewrite H2 H. simpl.
           do 2 rewrite kleisliVal.
           rewrite H3 H0.
           assert (forall (dn : nat_cpoType),
                      VInfToNat
                        (inNat dn)
                        =-=
                        eta dn
                  ).
           intros dn. by do 2 setoid_rewrite -> SUM_fun_simplx.
           do 2 rewrite H5.
           simpl. rewrite SmashLemmaValVal.
           2 : { split. apply tset_refl. apply tset_refl. }
           simpl. rewrite kleisliVal. by simpl.
           exists (SemOrdOp op xv xv'). auto.
        ** SSSCase "iv = Nat ∧ iv' = Bool".
           rewrite H4. destruct iv'.
           eapply anti_step. 2 : { apply BoolCast. } apply RE_eq_Fullset.
           eapply anti_step. 2 : { apply BoolCast. }
           eapply anti_step. 2 : { apply DOOp. }
           specialize (ifs_in (iv', BOOL (SemOrdOp op xv (Op_B_to_N xv')))).
           unfold mrel, "↓r" in ifs_in.
           rewrite Min.min_l in ifs_in.
           2 : { apply Le.le_trans with (m:=iv.+1).
                 apply Le.le_trans with (m:=iv'.+1).
                 apply Le.le_n_Sn. apply Le.le_Sn_le.
                 apply iv'_le_iv. apply iv_le_i'.
           }
           apply ifs_in.
           unfold "∈", Ω. simpl.
           exists (inNat (B_to_N (SemOrdOp op xv (Op_B_to_N xv')))).
           split. simpl.
           rewrite H2 H. simpl.
           do 2 rewrite kleisliVal.
           rewrite H3 H0.
           assert (forall (dn : nat_cpoType),
                      VInfToNat
                        (inNat dn)
                        =-=
                        eta dn
                  ).
           intros dn. by do 2 setoid_rewrite -> SUM_fun_simplx.
           do 2 rewrite H5.
           simpl. rewrite SmashLemmaValVal.
           2 : { split. apply tset_refl. apply tset_refl. }
           simpl. rewrite kleisliVal. destruct xv'. auto. auto.
           exists (SemOrdOp op xv (Op_B_to_N xv')). auto.
           rewrite H1. destruct iv.
        ** SSSCase "iv = Bool ∧ iv' = Nat".
           eapply anti_step. 2 : { apply BoolCast. } apply RE_eq_Fullset.
           eapply anti_step. 2 : { apply BoolCast. }
           eapply anti_step. 2 : { apply IOOp. }
           apply (OAC_Gen_StepI (Le.le_S_n _ _
                                           (Le.le_Sn_le _ _ iv_le_i'))) in σ_A_η.
           specialize (e'_A_d' iv σ η σ_A_η).
           specialize (e'_A_d' (iv.+1, PUSHROOp op fs ⌊ Op_B_to_N xv ⌋)).
           unfold mrel at 2 in e'_A_d'.
           rewrite (Min.min_l _ _ (Le.le_n_Sn iv)) in e'_A_d'.
           apply e'_A_d'.
           eapply bbot_weakened.
           *** SSCase "Down Closed".
               intros w m n w_in n_le_m. eapply Ω_down_closed. apply w_in.
               apply n_le_m.
           *** SSCase "Proof".
               intros iv' iv'_in. unfold "↓r".
               destruct iv' as [iv' v']. intro iv'_le_iv.
               destruct iv'. apply RE_eq_Fullset.
               destruct iv'_in as [? [? [[xv' [? ?]] | [xv' [? ?]]]]].
               rewrite H4.
               eapply anti_step. 2 : { apply DOOp. }
               specialize (ifs_in (iv',
                                   BOOL (SemOrdOp op (Op_B_to_N xv) xv'))).
               unfold mrel, "↓r" in ifs_in.
               rewrite Min.min_l in ifs_in.
               2 : { apply Le.le_trans with (m:=iv.+2).
                     apply Le.le_trans with (m:=iv.+1).
                     apply Le.le_Sn_le. auto. auto. auto.
               }
               apply ifs_in.
               unfold "∈", Ω. simpl.
               exists (inNat (B_to_N (SemOrdOp op (Op_B_to_N xv) xv'))).
               split. simpl.
               rewrite H2 H. simpl.
               do 2 rewrite kleisliVal.
               rewrite H3 H0.
               assert (forall (dn : nat_cpoType),
                          VInfToNat
                            (inNat dn)
                            =-=
                            eta dn
                      ).
               intros dn. by do 2 setoid_rewrite -> SUM_fun_simplx.
               do 2 rewrite H5.
               simpl. rewrite SmashLemmaValVal.
               2 : { split. apply tset_refl. apply tset_refl. }
               simpl. rewrite kleisliVal. destruct xv. auto. auto.
               exists (SemOrdOp op (Op_B_to_N xv) xv'). auto.
        ** SSSCase "iv = Bool ∧ iv' = Bool".
           rewrite H4. destruct iv'.
           eapply anti_step. 2 : { apply BoolCast. } apply RE_eq_Fullset.
           eapply anti_step. 2 : { apply BoolCast. }
           eapply anti_step. 2 : { apply DOOp. }
           specialize (ifs_in (iv', BOOL (SemOrdOp op (Op_B_to_N xv)
                                                   (Op_B_to_N xv')))).
           unfold mrel, "↓r" in ifs_in.
           rewrite Min.min_l in ifs_in.
           2 : { do 2 apply Le.le_Sn_le.
                 apply Le.le_trans with (m:=iv.+1). auto.
                 apply Le.le_Sn_le. auto.
           }
           apply ifs_in.
           unfold "∈", Ω. simpl.
           exists (inNat (B_to_N (SemOrdOp op (Op_B_to_N xv) (Op_B_to_N xv')))).
           split. simpl.
           rewrite H2 H. simpl.
           do 2 rewrite kleisliVal.
           rewrite H3 H0.
           assert (forall (dn : nat_cpoType),
                      VInfToNat
                        (inNat dn)
                        =-=
                        eta dn
                  ).
           intros dn. by do 2 setoid_rewrite -> SUM_fun_simplx.
           do 2 rewrite H5.
           simpl. rewrite SmashLemmaValVal.
           2 : { split. apply tset_refl. apply tset_refl. }
           simpl. rewrite kleisliVal.
           destruct xv. destruct xv'. auto. auto. destruct xv'. auto. auto.
           exists (SemOrdOp op (Op_B_to_N xv) (Op_B_to_N xv')). auto.
Qed.

Lemma Case5 :
  forall (E : Env) (Γ : LCtx E) (op : BoolOp) (e e': Expr E)
    (d d' : SemEnv E =-> VInf _BOT),
    (Γ e⊢ e ◀̂ d ⦂ bool̂) -> (Γ e⊢ e' ◀̂ d' ⦂ bool̂) ->
    (Γ e⊢ (BOp op e e') ◀̂ (GenBoolOp (SemBoolOp op) d d') ⦂ bool̂).
Proof.
  intros E Γ op e e' d d' e_A_d e'_A_d'.
  intros i σ η σ_A_η. unfold "_ ◀ _ | _ ⦂ _". unfold btop. unfold bbot.
  eapply btop_weakened.
  - Case "Down Closed".
    intros fs m n H n_le_m. eapply bbot_down_closed. apply H. apply n_le_m.
  - Case "Proof".
    intros ifs ifs_in.
    unfold "_ ⎩ _ ⎭"; rewrite mapBOp; fold e ⎩ σ ⎭ ; fold e' ⎩ σ ⎭.
    destruct ifs as [i' fs].
    intros i'_le_i.
    destruct i'.
    apply RE_eq_Fullset.
    eapply anti_step. 2 : { apply SBOp. }
    apply (OAC_Gen_StepI i'_le_i) in σ_A_η.
    apply OAC_StepI in σ_A_η.
    specialize (e_A_d i' σ η σ_A_η).
    specialize (e_A_d (i'.+1, PUSHLBOp op fs (e' ⎩ σ ⎭))).
    unfold mrel at 2 in e_A_d.
    rewrite (Min.min_l _ _ (Le.le_n_Sn i')) in e_A_d.
    apply e_A_d.
    eapply bbot_weakened.
    + SCase "Down Closed".
      intros v m n v_in n_le_m. eapply Ω_down_closed. apply v_in. apply n_le_m.
    + SCase "Proof".
      intros iv iv_in.
      destruct iv as [iv v].
      intro iv_le_i'. unfold "↓r".
      destruct iv. apply RE_eq_Fullset.
      destruct iv_in as [? [? [xv [? ?]]]].
      rewrite H1.
      eapply anti_step. 2 : { apply IBOp. }
      apply (OAC_Gen_StepI (Le.le_S_n _ _ iv_le_i')) in σ_A_η.
      specialize (e'_A_d' iv σ η σ_A_η).
      specialize (e'_A_d' (iv.+1, PUSHRBOp op fs ⎣ xv ⎦)).
      unfold mrel at 2 in e'_A_d'.
      rewrite (Min.min_l _ _ (Le.le_n_Sn iv)) in e'_A_d'.
      apply e'_A_d'.
      eapply bbot_weakened.
      * SSCase "Down Closed".
        intros w m n w_in n_le_m. eapply Ω_down_closed. apply w_in. apply n_le_m.
      * SSCase "Proof".
        intros iv' iv'_in. unfold "↓r".
        destruct iv' as [iv' v']. intro iv'_le_iv.
        destruct iv'. apply RE_eq_Fullset.
        destruct iv'_in as [? [? [xv' [? ?]]]].
        rewrite H4.
        eapply anti_step. 2 : { apply DBOp. }
        specialize (ifs_in (iv', BOOL (SemBoolOp op xv xv'))).
        unfold mrel, "↓r" in ifs_in.
        rewrite Min.min_l in ifs_in.
        2 : { apply Le.le_trans with (m:=iv.+1).
              apply Le.le_trans with (m:=iv'.+1).
              apply Le.le_n_Sn. apply iv'_le_iv. apply iv_le_i'.
        }
        apply ifs_in.
        unfold "∈", Ω.
        exists (inNat (B_to_N (SemBoolOp op xv xv'))).
        split. simpl.
        rewrite H2 H. simpl.
        do 2 rewrite kleisliVal.
        rewrite H3 H0.
        assert (forall (dn : bool_cpoType),
                   VInfToBool
                     (inNat (B_to_N dn))
                     =-=
                     eta dn
               ).
        intros dn. do 2 setoid_rewrite -> SUM_fun_simplx. simpl. destruct dn.
        auto. auto.
        do 2 rewrite -> H5.
        simpl. rewrite SmashLemmaValVal.
        2 : { split. apply tset_refl. apply tset_refl. }
        simpl. rewrite kleisliVal. by simpl.
        exists (SemBoolOp op xv xv'). auto.
Qed.

Lemma Case6 :
  forall (E : Env) (Γ : LCtx E) (op : NatOp) (e e': Expr E)
    (d d' : SemEnv E =-> VInf _BOT),
    (Γ e⊢ e ◀̂ d ⦂ nat̂) -> (Γ e⊢ e' ◀̂ d' ⦂ nat̂) ->
    (Γ e⊢ (NOp op e e') ◀̂ (⦓SemNatOp op⦔ d d') ⦂ nat̂).
Proof.
  intros E Γ op e e' d d' e_A_d e'_A_d'.
  intros i σ η σ_A_η. unfold "_ ◀ _ | _ ⦂ _". unfold btop. unfold bbot.
  eapply btop_weakened.
  - Case "Down Closed".
    intros fs m n H n_le_m. eapply bbot_down_closed. apply H. apply n_le_m.
  - Case "Proof".
    intros ifs ifs_in.
    unfold "_ ⎩ _ ⎭"; rewrite mapNOp; fold e ⎩ σ ⎭ ; fold e' ⎩ σ ⎭.
    destruct ifs as [i' fs].
    intros i'_le_i.
    destruct i'.
    apply RE_eq_Fullset.
    eapply anti_step. 2 : { apply SNOp. }
    apply (OAC_Gen_StepI i'_le_i) in σ_A_η.
    apply OAC_StepI in σ_A_η.
    specialize (e_A_d i' σ η σ_A_η).
    specialize (e_A_d (i'.+1, fs ∘  ( ⊡  ⦓ op ⦔ e' ⎩ σ ⎭))).
    unfold mrel at 2 in e_A_d.
    rewrite (Min.min_l _ _ (Le.le_n_Sn i')) in e_A_d.
    apply e_A_d.
    eapply bbot_weakened.
    + SCase "Down Closed".
      intros v m n v_in n_le_m. eapply Ω_down_closed. apply v_in. apply n_le_m.
    + SCase "Proof".
      intros iv iv_in.
      destruct iv as [iv v].
      intro iv_le_i'. unfold "↓r".
      destruct iv. apply RE_eq_Fullset.
      destruct iv_in as [? [? [[xv [? ?]] | [xv [? ?]]]]].
      ++ SSCase "v = Nat".
         rewrite H1.
         eapply anti_step. 2 : { apply INOp. }
         apply (OAC_Gen_StepI (Le.le_S_n _ _ iv_le_i')) in σ_A_η.
         specialize (e'_A_d' iv σ η σ_A_η).
         specialize (e'_A_d' (iv.+1, PUSHRNOp op fs ⌊xv⌋)).
         unfold mrel at 2 in e'_A_d'.
         rewrite (Min.min_l _ _ (Le.le_n_Sn iv)) in e'_A_d'.
         apply e'_A_d'.
         eapply bbot_weakened.
         +++ SSSCase "Down Closed".
             intros w m n w_in n_le_m. eapply Ω_down_closed. apply w_in.
             apply n_le_m.
         +++ SSSCase "Proof".
             intros iv' iv'_in. unfold "↓r".
             destruct iv' as [iv' v']. intro iv'_le_iv.
             destruct iv'. apply RE_eq_Fullset.
             destruct iv'_in as [? [? [[xv' [? ?]] | [xv' [? ?]]]]].
             ++++ SSSSCase "v' = Nat".
                  rewrite H4.
                  eapply anti_step. 2 : { apply DNOp. }
                  specialize (ifs_in (iv', NAT (SemNatOp op xv xv'))).
                  unfold mrel, "↓r" in ifs_in.
                  rewrite Min.min_l in ifs_in.
                  2 : { apply Le.le_trans with (m:=iv.+1).
                        apply Le.le_trans with (m:=iv'.+1).
                        apply Le.le_n_Sn. apply iv'_le_iv. apply iv_le_i'.
                  }
                  apply ifs_in.
                  unfold "∈", Ω.
                  exists (inNat (SemNatOp op xv xv')).
                  split. simpl.
                  rewrite H2 H. simpl.
                  do 2 rewrite kleisliVal.
                  rewrite H3 H0.
                  assert (forall (dn : nat_cpoType),
                             VInfToNat
                               (inNat dn)
                               =-=
                               eta dn
                         ).
                  intros dn.
                    by do 2 setoid_rewrite -> SUM_fun_simplx.
                    do 2 rewrite H5.
                    simpl. rewrite SmashLemmaValVal.
                    2 : { split. apply tset_refl. apply tset_refl. }
                    simpl. rewrite kleisliVal. by simpl.
                    left. exists (SemNatOp op xv xv'). auto.
             ++++ SSSSCase "v' = Bool".
                  rewrite H4. destruct iv'.
                  eapply anti_step. 2 : { apply BoolCast. } apply RE_eq_Fullset.
                  eapply anti_step. 2 : { apply BoolCast. }
                  eapply anti_step. 2 : { apply DNOp. }
                  specialize (ifs_in (iv', NAT (SemNatOp op xv (Op_B_to_N xv')))).
                  unfold mrel, "↓r" in ifs_in.
                  rewrite Min.min_l in ifs_in.
                  2 : { apply Le.le_Sn_le.
                        apply Le.le_trans with (m:=iv.+1).
                        apply Le.le_Sn_le. auto.  auto.
                  }
                  apply ifs_in.
                  unfold "∈", Ω.
                  exists (inNat (SemNatOp op xv (Op_B_to_N xv'))).
                  split. simpl.
                  rewrite H2 H. simpl.
                  do 2 rewrite kleisliVal.
                  rewrite H3 H0.
                  assert (forall (dn : nat_cpoType),
                             VInfToNat
                               (inNat dn)
                               =-=
                               eta dn
                         ).
                  intros dn.
                    by do 2 setoid_rewrite -> SUM_fun_simplx.
                    do 2 rewrite H5.
                    simpl. rewrite SmashLemmaValVal.
                    2 : { split. apply tset_refl. apply tset_refl. }
                    simpl. rewrite kleisliVal. destruct xv'. auto. auto.
                    left. exists (SemNatOp op xv (Op_B_to_N xv')). auto.
      ++ SSCase "v = Bool".
         rewrite H1. destruct iv.
         eapply anti_step. 2 : { apply BoolCast. } apply RE_eq_Fullset.
         eapply anti_step. 2 : { apply BoolCast. }
         eapply anti_step. 2 : { apply INOp. }
         apply (OAC_Gen_StepI (Le.le_S_n _ _
                                           (Le.le_Sn_le _ _ iv_le_i'))) in σ_A_η.
         specialize (e'_A_d' iv σ η σ_A_η).
         specialize (e'_A_d' (iv.+1, PUSHRNOp op fs ⌊ Op_B_to_N xv ⌋)).
         unfold mrel at 2 in e'_A_d'.
         rewrite (Min.min_l _ _ (Le.le_n_Sn iv)) in e'_A_d'.
         apply e'_A_d'.
         eapply bbot_weakened.
         +++ SSSCase "Down Closed".
             intros w m n w_in n_le_m. eapply Ω_down_closed. apply w_in.
             apply n_le_m.
         +++ SSSCase "Proof".
             intros iv' iv'_in. unfold "↓r".
             destruct iv' as [iv' v']. intro iv'_le_iv.
             destruct iv'. apply RE_eq_Fullset.
             destruct iv'_in as [? [? [[xv' [? ?]] | [xv' [? ?]]]]].
             ++++ SSSSCase "v' = Nat".
                  rewrite H4.
                  eapply anti_step. 2 : { apply DNOp. }
                  specialize(ifs_in (iv', NAT (SemNatOp op (Op_B_to_N xv) xv'))).
                  unfold mrel, "↓r" in ifs_in.
                  rewrite Min.min_l in ifs_in.
                  2 : { apply Le.le_Sn_le.
                        apply Le.le_trans with (m:=iv.+1). auto.
                        apply Le.le_Sn_le. auto.
                  }
                  apply ifs_in.
                  unfold "∈", Ω.
                  exists (inNat (SemNatOp op (Op_B_to_N xv) xv')).
                  split. simpl.
                  rewrite H2 H. simpl.
                  do 2 rewrite kleisliVal.
                  rewrite H3 H0.
                  assert (forall (dn : nat_cpoType),
                             VInfToNat
                               (inNat dn)
                               =-=
                               eta dn
                         ).
                  intros dn.
                    by do 2 setoid_rewrite -> SUM_fun_simplx.
                    do 2 rewrite H5.
                    simpl. rewrite SmashLemmaValVal.
                    2 : { split. apply tset_refl. apply tset_refl. }
                    simpl. rewrite kleisliVal. destruct xv. auto. auto.
                    left. exists (SemNatOp op (Op_B_to_N xv) xv'). auto.
             ++++ SSSSCase "v' = Bool".
                  rewrite H4. destruct iv'.
                  eapply anti_step. 2 : { apply BoolCast. } apply RE_eq_Fullset.
                  eapply anti_step. 2 : { apply BoolCast. }
                  eapply anti_step. 2 : { apply DNOp. }
                  specialize (ifs_in (iv', NAT (SemNatOp op
                                                         (Op_B_to_N xv)
                                                         (Op_B_to_N xv')))).
                  unfold mrel, "↓r" in ifs_in.
                  rewrite Min.min_l in ifs_in.
                  2 : { do 2 apply Le.le_Sn_le.
                        apply Le.le_trans with (m:=iv.+1). auto.
                        apply Le.le_Sn_le. auto.
                  }
                  apply ifs_in.
                  unfold "∈", Ω.
                  exists (inNat (SemNatOp op (Op_B_to_N xv) (Op_B_to_N xv'))).
                  split. simpl.
                  rewrite H2 H. simpl.
                  do 2 rewrite kleisliVal.
                  rewrite H3 H0.
                  assert (forall (dn : nat_cpoType),
                             VInfToNat
                               (inNat dn)
                               =-=
                               eta dn
                         ).
                  intros dn.
                    by do 2 setoid_rewrite -> SUM_fun_simplx.
                    do 2 rewrite H5.
                    simpl. rewrite SmashLemmaValVal.
                    2 : { split. apply tset_refl. apply tset_refl. }
                    simpl. rewrite kleisliVal.
                    destruct xv. destruct xv'. auto. auto.
                    destruct xv'. auto. auto.
                    left. exists (SemNatOp op  (Op_B_to_N xv) (Op_B_to_N xv')). auto.
Qed.

Lemma Case7 : forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
                (e : Expr E) (e' : Expr E.+1)
                (d  : SemEnv E    =-> VInf _BOT)
                (d' : SemEnv E.+1 =-> VInf _BOT),
    (Γ e⊢ e ◀̂ d ⦂ θ') -> ((θ' × Γ) e⊢ e' ◀̂ d' ⦂ θ) ->
    (Γ e⊢ (LET e e') ◀̂ (d' ⊥⊥⃑ d) ⦂ θ).
Proof.
  intros θ θ' E Γ e e' d d' e_A_d e'_A_d'.
  intros i σ η σ_A_η.
  eapply btop_weakened.
  - Case "Down Closed".
    intros fs m n H n_le_m. eapply bbot_down_closed. apply H. apply n_le_m.
  - Case "Proof".
    intros ifs ifs_in.
    unfold "_ ⎩ _ ⎭"; rewrite mapLET; fold e ⎩ σ ⎭;
    fold e' ⎩ lift SubMapOps σ ⎭; fold liftSub.
    destruct ifs as [i' fs].
    intros i'_le_i.
    destruct i'.
    apply RE_eq_Fullset.
    eapply anti_step. 2 : { apply SLet. }
    apply (OAC_Gen_StepI i'_le_i) in σ_A_η.
    apply OAC_StepI in σ_A_η.
    specialize (e_A_d i' σ η σ_A_η).
    specialize (e_A_d (i'.+1, fs ⊚ (e' ⎩ liftSub σ ⎭))).
    unfold mrel at 2 in e_A_d.
    rewrite (Min.min_l _ _ (Le.le_n_Sn i')) in e_A_d.
    apply e_A_d.
    eapply bbot_weakened.
    + SCase "Down Closed".
      intros v m n v_in n_le_m. eapply Ω_down_closed. apply v_in. apply n_le_m.
    + SCase "Proof".
      intros iv iv_in.
      destruct iv as [iv v].
      intro iv_le_i'. unfold "↓r".
      destruct iv. apply RE_eq_Fullset.
      eapply anti_step. 2 : { apply Subst. }
      destruct iv_in as [dv [? ?]].
      assert (σ'_A_η' : @OperApproxCtx E.+1 (θ' × Γ) iv
                                    (composeSub [v] (liftSub σ)) (η,dv)).
      * SSCase "Defining the extension of [σ, v] ▷ (η,dv)".
        intro w. dependent destruction w.
        -- SSSCase "w = ZVAR".
           simpl. rewrite -> (fst (substComposeSub _)). unfold "_ ⎧ _ ⎫".
           rewrite -> mapVAR. simpl. rewrite -> mapVAR. simpl.
           apply OAV_StepI in H0. apply H0.
        -- SSSCase "w = SVAR".
           simpl. rewrite -> (fst (substComposeSub _)). unfold "_ ⎧ _ ⎫".
           rewrite -> mapVAR. simpl. unfold renV.
           rewrite <- (fst (applyComposeRen _)).
           unfold composeRen. simpl. unfold idSub.
           rewrite -> (fst (applyIdMap _ _)).
           apply (OAC_Gen_StepI (Le.le_S_n _ _ iv_le_i')) in σ_A_η.
           apply σ_A_η.
      specialize (e'_A_d' iv _ _ σ'_A_η').
      specialize (e'_A_d' (iv.+1, fs)).
      unfold mrel at 2 in e'_A_d'.
      rewrite (Min.min_l _ _ (Le.le_n_Sn iv)) in e'_A_d'.
      rewrite <- (snd (substComposeSub _)).
      apply e'_A_d'.
      eapply bbot_weakened.
      * SSCase "Down Closed".
        intros w m n w_in n_le_m. eapply Ω_down_closed. apply w_in. apply n_le_m.
      * SSCase "Proof".
        intros iw iw_in.
        destruct iw as [iw w].
        intros iw_le_iv. unfold "↓r".
        specialize (ifs_in (iw, w)).
        unfold mrel, "↓r" in ifs_in.
        rewrite Min.min_l in ifs_in.
        2 : { apply Le.le_trans with (m:=iv.+1). 
              apply iw_le_iv. apply iv_le_i'.
        }
        apply ifs_in.
        destruct iw_in as [dw [? ?]].
        exists dw. split. simpl. rewrite H.
        rewrite KLEISLIR_unit2. apply H1.
        apply H2.
Qed.
    
Lemma Case8 : forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
                (f v : V E)
                (df : SemEnv E =-> VInf)
                (dv : SemEnv E =-> VInf),
    (Γ v⊢ f ◁̂ df ⦂ θ' ⇥ θ) ->
    (Γ v⊢ v ◁̂ dv ⦂ θ') ->
    (Γ e⊢ (f @ v) ◀̂ (df↓f dv) ⦂ θ).
Proof.
  intros θ θ' E Γ f v df dv f_A_df v_A_dv.
  intros i σ η σ_A_η.
  eapply btop_weakened.
  - Case "Down Closed".
    intros fs m n H n_le_m. eapply bbot_down_closed. apply H. apply n_le_m.
  - Case "Proof".
    intros ifs ifs_in.
    destruct ifs as [i' fs].
    intro i'_le_i.
    unfold "_ ⎩ _ ⎭"; rewrite mapAPP; fold f ⎧ σ ⎫ v ⎧ σ ⎫.
    destruct i'.
    apply RE_eq_Fullset.
    apply (OAC_Gen_StepI i'_le_i) in σ_A_η.
    specialize (f_A_df i'.+1 σ η σ_A_η).
    destruct f_A_df as [eb [? [df' [? ?]]]].
    rewrite H.
    eapply anti_step. 2 : { apply App. }
    apply OAC_StepI in σ_A_η.
    specialize (v_A_dv i' σ η σ_A_η).
    specialize (H1 i' (v ⎧ σ ⎫) (dv η) (Lt.lt_n_Sn _) v_A_dv).
    specialize (H1 (i'.+1, fs)). simpl in H1.
    rewrite Min.min_l in H1. 2 : { apply Le.le_n_Sn. }
    apply H1.
    eapply FS_In_compat. 2 : { apply ifs_in. }
    simpl. rewrite H0.
    assert (VInfToFun (inFun df')
            =-=
            eta df'
           ).
    + SCase "Assert".
      rewrite <- comp_simpl. by rewrite -> VInfToFun_Fun. 
    rewrite H2. rewrite KLEISLIL_unit2. by simpl.
Qed.

Lemma Case9 :
  forall (E : Env) (Γ : LCtx E) (θ : LType) (e0 e1 e2 : Expr E)
    (b     : SemEnv E =-> VInf _BOT)
    (d1 d2 : SemEnv E =-> VInf _BOT),
    (Γ e⊢ e0 ◀̂ b ⦂ bool̂) -> (Γ e⊢ e1 ◀̂ d1 ⦂ θ) -> (Γ e⊢ e2 ◀̂ d2 ⦂ θ) ->
    (Γ e⊢ IFB e0 e1 e2 ◀̂ (IfOneOp b d1 d2) ⦂ θ).
Proof.
  intros E Γ θ e0 e1 e2 b d1 d2 e0_A_b e1_A_d1 e2_A_d2.
  intros i σ η σ_A_η.
  eapply btop_weakened.
  - Case "Down Closed".
    intros fs m n H n_le_m. eapply bbot_down_closed. apply H. apply n_le_m.
  - Case "Proof".
    intros ifs ifs_in.
    destruct ifs as [i' fs].
    intro i'_le_i.
    unfold "_ ⎩ _ ⎭"; rewrite mapIFB ; fold e0 ⎩ σ ⎭ e1 ⎩ σ ⎭ e2 ⎩ σ ⎭.
    destruct i'.
    apply RE_eq_Fullset.
    apply (OAC_Gen_StepI i'_le_i) in σ_A_η. apply OAC_StepI in σ_A_η.
    eapply anti_step. 2 : { apply IfB. }
    specialize (e0_A_b i' σ η σ_A_η).
    specialize (e0_A_b (i', fs ∘  (e1 ⎩ σ ⎭ ⇆ e2 ⎩ σ ⎭))).
    unfold mrel at 2 in e0_A_b. rewrite Min.min_idempotent in e0_A_b.
    apply e0_A_b.
    eapply bbot_weakened.
    + SCase "Down Closed".
        intros w m n w_in n_le_m. eapply Ω_down_closed. apply w_in. apply n_le_m.
    + SCase "Proof".
      intros iv0 iv0_in.
      destruct iv0 as [iv0 v0].
      destruct iv0_in as [bv [? [b' [? ?]]]].
      destruct b'. unfold "↓r".
      * SSCase "b = true".
        intro iv0_le_i'.
        rewrite H1.
        destruct iv0. apply RE_eq_Fullset.
        eapply anti_step. 2 : { apply IfBT. }
        apply OAC_Gen_StepI with (j:=iv0.+1) in σ_A_η. 2 : { apply iv0_le_i'. }
        specialize (e1_A_d1 iv0.+1 σ η σ_A_η).
        apply OAE_StepI in e1_A_d1.
        specialize (e1_A_d1 (i'.+1, fs)).
        unfold mrel at 2 in e1_A_d1.
        rewrite Min.min_l in e1_A_d1.
        2 : { apply Le.le_trans with (m:=i').
              apply Le.le_Sn_le. apply iv0_le_i'.
              apply Le.le_n_Sn.
        }
        apply e1_A_d1.
        assert ((IfOneOp b d1 d2) η =-= d1 η).
        -- SSSCase "Assert".
           simpl. rewrite H H0. simpl.
           rewrite kleisliVal.
           assert (VInfToNat (inNat 1)
                     =-=
                     eta 1
                  ) by (rewrite <- comp_simpl; by rewrite -> VInfToNat_Nat).
           rewrite H2. clear H2.
           by rewrite KLEISLIL_unit2.
        apply FS_In_compat with (d':=d1 η) in ifs_in.
        apply ifs_in.
        apply H2.
      * SSCase "b = false".
        intro iv0_le_i'.
        rewrite H1.
        destruct iv0. apply RE_eq_Fullset.
        eapply anti_step. 2 : { apply IfBF. }
        apply OAC_Gen_StepI with (j:=iv0.+1) in σ_A_η. 2 : { apply iv0_le_i'. }
        specialize (e2_A_d2 iv0.+1 σ η σ_A_η).
        apply OAE_StepI in e2_A_d2.
        specialize (e2_A_d2 (i'.+1, fs)).
        unfold mrel at 2 in e2_A_d2.
        rewrite Min.min_l in e2_A_d2.
        2 : { apply Le.le_trans with (m:=i').
              apply Le.le_Sn_le. apply iv0_le_i'.
              apply Le.le_n_Sn.
        }
        apply e2_A_d2.
        assert ((IfOneOp b d1 d2) η =-= d2 η).
        -- SSSCase "Assert".
           simpl. rewrite H H0. simpl.
           rewrite kleisliVal.
           assert (VInfToNat (inNat 0)
                     =-=
                     eta 0
                  ) by (rewrite <- comp_simpl; by rewrite -> VInfToNat_Nat).
           rewrite H2. clear H2.
           by rewrite KLEISLIL_unit2.
        apply FS_In_compat with (d':=d2 η) in ifs_in.
        apply ifs_in.
        apply H2.
Qed.

Lemma Case10 : forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
                (v v' : V E)
                (dv dv' : SemEnv E =-> VInf),
    (Γ v⊢ v ◁̂ dv ⦂ θ) ->
    (Γ v⊢ v' ◁̂ dv' ⦂ θ') ->
    (Γ v⊢ VPAIR v v' ◁̂ PairOp dv dv' ⦂ θ ⨱ θ').
Proof.
  intros θ θ' E Γ v v' dv dv' IH IH'.
  intros i σ η σ_A_η.
  exists v ⎧ σ ⎫, v' ⎧ σ ⎫. split. auto.
  exists (Roll (dv η)), (Roll (dv' η)). split. by simpl.
  intros j H. split.
  eapply OAV_compat. symmetry. apply URid.
  eapply OAV_Gen_StepI. apply PeanoNat.Nat.lt_le_incl. apply H. apply IH. auto.
  eapply OAV_compat. symmetry. apply URid.
  eapply OAV_Gen_StepI. apply PeanoNat.Nat.lt_le_incl. apply H. apply IH'. auto.
Qed.

Lemma Case11 :
  forall (E : Env) (Γ : LCtx E) (θ θ' : LType) (v : V E)
    (dv : SemEnv E =-> VInf),
    (Γ v⊢ v ◁̂ dv ⦂ θ ⨱ θ') ->
    (Γ e⊢ (EFST v) ◀̂ (FSTOp dv) ⦂ θ).
Proof.
  intros E Γ θ θ' v dv IH.
  intros i σ η σ_A_η.
  eapply btop_weakened.
  - Case "Down Closed".
    intros fs m n H n_le_m. eapply bbot_down_closed. apply H. apply n_le_m.
  - Case "Proof".
    intros ifs ifs_in.
    destruct ifs as [i' fs].
    intro i'_le_i.
    unfold "_ ⎩ _ ⎭"; rewrite mapFST ; fold v ⎧ σ ⎫.
    destruct i'.
    apply RE_eq_Fullset.
    assert (IH':=IH).
    specialize (IH' _ _ _ σ_A_η).
    destruct IH' as [v' [v'' [veq [dv1 [dv2 [? ?]]]]]].
    apply (OAC_Gen_StepI i'_le_i) in σ_A_η. apply OAC_StepI in σ_A_η.
    rewrite -> veq.
    eapply anti_step. 2 : { apply FstOp. }
    specialize (H0 i' i'_le_i). destruct H0.
    specialize (ifs_in (i',v')). simpl in ifs_in.
    rewrite -> (Min.min_l i' (i'.+1) (Le.le_n_Sn i')) in ifs_in.
    apply ifs_in.
    eapply Omega_compat. rewrite -> H. simpl.
    setoid_rewrite -> SUM_fun_simplx. simpl.
    rewrite kleisliVal. simpl. reflexivity.
    exists (Unroll dv1). split. auto. auto.
Qed. 

Lemma Case12 :
  forall (E : Env) (Γ : LCtx E) (θ θ' : LType) (v : V E)
    (dv : SemEnv E =-> VInf),
    (Γ v⊢ v ◁̂ dv ⦂ θ ⨱ θ') ->
    (Γ e⊢ (ESND v) ◀̂ (SNDOp dv) ⦂ θ').
Proof.
  intros E Γ θ θ' v dv IH.
  intros i σ η σ_A_η.
  eapply btop_weakened.
  - Case "Down Closed".
    intros fs m n H n_le_m. eapply bbot_down_closed. apply H. apply n_le_m.
  - Case "Proof".
    intros ifs ifs_in.
    destruct ifs as [i' fs].
    intro i'_le_i.
    unfold "_ ⎩ _ ⎭"; rewrite mapSND ; fold v ⎧ σ ⎫.
    destruct i'.
    apply RE_eq_Fullset.
    assert (IH':=IH).
    specialize (IH' _ _ _ σ_A_η).
    destruct IH' as [v' [v'' [veq [dv1 [dv2 [? ?]]]]]].
    apply (OAC_Gen_StepI i'_le_i) in σ_A_η. apply OAC_StepI in σ_A_η.
    rewrite -> veq.
    eapply anti_step. 2 : { apply SndOp. }
    specialize (H0 i' i'_le_i). destruct H0.
    specialize (ifs_in (i',v'')). simpl in ifs_in.
    rewrite -> (Min.min_l i' (i'.+1) (Le.le_n_Sn i')) in ifs_in.
    apply ifs_in.
    eapply Omega_compat. rewrite -> H. simpl.
    setoid_rewrite -> SUM_fun_simplx. simpl.
    rewrite kleisliVal. simpl. reflexivity.
    exists (Unroll dv2). split. auto. auto.
Qed. 

Lemma PF_subs_V : forall (θ θ' : LType) (v : V 0)
                  (tjs : (θ t≤ θ')) (dv : VInf),
    forall (i : nat), (v ◁i| dv ⦂ θ) -> (v ◁i| dv ⦂ θ').
Proof.
  intros θ θ' v tjs dv i H.
  generalize dependent v.
  dependent induction tjs.
  - Case "bool ≤ nat".
    intros v H. simpl in *.
    destruct H as [b [? ?]]. right.
    exists b. split. auto. auto.
  - Case "θ ≤ θ".
    auto.
  - Case "θ ≤ θ' ∧ θ' ≤ θ''".
    auto.
  - Case "(θ0,θ1) ≤ (θ0',θ1')".
    intros v H.
    destruct H as [pv1 [pv2 [? [dv1 [dv2 [? ?]]]]]].
    exists pv1, pv2. split. auto. exists dv1, dv2. split. auto.
    intros n' H2. specialize (H1 n' H2) as [? ?].
    split.
    apply IHtjs1. auto.
    apply IHtjs2. auto.
  - Case "θ0 ⇥ θ1 x y ≤ θ0' ⇥ θ1'".
    intros v H.
    destruct H as [e [? [f [? ?]]]].
    exists e. split. auto. exists f. split. auto.
    intros n' w dw H2 H3.
    specialize (IHtjs1 _ _ _ H3).
    specialize (H1 _ _ _ H2 IHtjs1).
    intros fs fs_in. apply H1.
    intros (i',a) H4. apply fs_in.
    destruct H4 as [? [? ?]].
    specialize (IHtjs2 _ _ _ H5).
    exists x. auto.
Qed.

Lemma PF_subs_E : forall (θ θ' : LType) (e : Expr 0)
                  (tjs : (θ t≤ θ')) (de : VInf _BOT),
    forall (i : nat), (e ◀i| de ⦂ θ) -> (e ◀i| de ⦂ θ').
Proof.
  intros θ θ' e tjs de i H.
  intros (i',fs) fs_in.
  apply H. intros (i'',a) H'.
  apply fs_in. destruct H' as [? [? ?]].
  exists x. split. auto. apply PF_subs_V with (θ:=θ). auto. auto.
Qed.

Lemma PF_subs_V' : forall (E : Env) (Γ : LCtx E) (θ θ' : LType) (v : V E)
                     (tjs : (θ t≤ θ')) (dv : SemEnv E =-> VInf),
    (Γ v⊢ v ◁̂ dv ⦂ θ) -> (Γ v⊢ v ◁̂ dv ⦂ θ').
Proof.
  intros E Γ θ θ' v tjs dv H.
  intros i σ η σ_A_η.
  apply PF_subs_V with (θ:=θ). auto. auto.
Qed.

Lemma PF_subs_E' : forall (E : Env) (Γ : LCtx E) (θ θ' : LType) (e : Expr E)
                     (tjs : (θ t≤ θ')) (de : SemEnv E =-> VInf _BOT),
    (Γ e⊢ e ◀̂ de ⦂ θ) -> (Γ e⊢ e ◀̂ de ⦂ θ').
Proof.
  intros E Γ θ θ' v tjs dv H.
  intros i σ η σ_A_η.
  apply PF_subs_E with (θ:=θ). auto. auto.
Qed.

(** *Theorem 5: Fundamental Property of Logical Relations *)
Lemma FundamentalPropOfLogicalRelations : forall (E : Env),
    (forall (v : V E) (Γ : LCtx E) (θ : LType) (tj : (Γ v⊢ v ⦂ θ)),
        (Γ v⊢ v ◁̂ ⟦ v ⟧v ⦂ θ))
    /\
    (forall (e : Expr E) (Γ : LCtx E) (θ : LType) (tj : (Γ e⊢ e ⦂ θ)),
        (Γ e⊢ e ◀̂ ⟦ e ⟧e ⦂ θ)).
Proof.
  apply mutual_VE_induction.
  - Case "v = VAR".
    intros E v Γ θ tj.
    dependent induction tj. apply Case1.
    apply PF_subs_V' with (θ:=θ). auto. auto.
  - Case "v = BOOL".
    intros E b Γ θ tj. dependent induction tj.
    simpl.
    intros i σ η σ_A_η.
    exists b. split. auto.  auto.
    apply PF_subs_V' with (θ:=θ). auto. auto.
  - Case "v = NAT".
    intros E n Γ θ tj. dependent induction tj.
    simpl.
    intros i σ η σ_A_η.
    left. exists n. auto.
    apply PF_subs_V' with (θ:=θ). auto. auto.
  - Case "v = FUN".
    intros E e IHe Γ θ tj. dependent induction tj.
    apply Case2. apply IHe. apply t.
    apply PF_subs_V' with (θ:=θ). auto. auto.
  - Case "v = PAIR".
    intros E v IH v' IH' Γ θ tj. dependent induction tj.
    apply Case10. apply IH. auto. apply IH'. auto.
    apply PF_subs_V' with (θ:=θ). auto. auto.
  - Case "e = VAL".
    intros E v IH Γ θ tj. dependent induction tj.
    apply Case3. apply IH. apply t.
    apply PF_subs_E' with (θ:=θ). auto. auto.
  - Case "e = APP".
    intros E f IHf v IHv Γ θ tj. dependent induction tj.
    apply Case8 with (θ':=θ'). apply IHf. apply t. apply IHv. apply t0.
    apply PF_subs_E' with (θ:=θ). auto. auto.
  - Case "e = OOp".
    intros E op e IHe e' IHe' Γ θ tj. dependent induction tj.
    apply Case4. apply IHe. apply tj1. apply IHe'. apply tj2.
    apply PF_subs_E' with (θ:=θ). auto. auto.
  - Case "e = BOp".
    intros E op e IHe e' IHe' Γ θ tj. dependent induction tj.
    apply Case5. apply IHe. apply tj1. apply IHe'. apply tj2.
    apply PF_subs_E' with (θ:=θ). auto. auto.
  - Case "e = NOp".
    intros E op e IHe e' IHe' Γ θ tj. dependent induction tj.
    apply Case6. apply IHe. apply tj1. apply IHe'. apply tj2.
    apply PF_subs_E' with (θ:=θ). auto. auto.
  - Case "e = LET".
    intros E e IHe e' IHe' Γ θ tj. dependent induction tj.
    apply Case7 with (θ':=θ'). apply IHe. apply tj1. apply IHe'. apply tj2.
    apply PF_subs_E' with (θ:=θ). auto. auto.
  - Case "e = IFB".
    intros E b IHb e1 IHe1 e2 IHe2 Γ θ tj. dependent induction tj.
    apply Case9. apply IHb. apply tj1.
    apply IHe1. apply tj2. apply IHe2. apply tj3.
    apply PF_subs_E' with (θ:=θ). auto. auto.
  - Case "e = FST".
    intros E v IH Γ θ tj. dependent induction tj.
    eapply Case11. apply IH. apply t.
    apply PF_subs_E' with (θ:=θ). auto. auto.
  - Case "e = SND".
    intros E v IH Γ θ tj. dependent induction tj.
    eapply Case12. apply IH. apply t.
    apply PF_subs_E' with (θ:=θ). auto. auto.
Qed.

End OperApprox.
