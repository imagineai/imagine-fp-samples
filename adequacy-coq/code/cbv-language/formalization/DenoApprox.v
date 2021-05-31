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
Require Import Sets.

Require Import domoprs.
Require Import PredomAll.
Require Import uniirec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.

Notation "x ∉ X" := (~ (In _ X x)) (at level 1, no associativity).
Notation "x ∈ X" := (In _ X x) (at level 1, no associativity).
(*end hide*)
(** *)
(*** Section 5: ADEQUACY ***)
(** *)

(** *Observation *)
Definition AntiexecE (R : Rel (Expr 0) FS) : Prop :=
  forall (e e' : Expr 0) (E E' : FS),
    R e E -> ((E', e') ⟼⋆ (E, e)) -> R e' E'
.

Record RelE := mkrelE {
   rel      :> Rel (Expr 0) FS;
   antiExec :> AntiexecE rel
}.

Section DenoApprox.
  
Variable RE : RelE.
  
Require Import Relations.Relation_Operators.
  
(** Denotational approximation *)

Definition DownR : Rel (Expr 0) FS -> Rel (V 0) FS := fun R v E => R (VAL v) E.
Notation "'↓r' X" := (DownR X) (at level 1, no associativity).
Notation "↓ X" := (bbot (↓r RE) X) (at level 1, no associativity).
Notation "⇑ X" := (btop RE X) (at level 1, no associativity).

Definition Ω (θ : LType) (de : (SemType θ))  (DR : V 0 -> SemType θ -> Prop) :
  Power_set (V 0) :=
  fun (v : V 0) => DR v de
.

(** *Definition 52: Denotational approximation of values *)
Fixpoint DenotApproxV (θ : LType) : V 0 -> SemType θ -> Prop :=
  match θ as θ return V 0 -> SemType θ -> Prop with
  | bool̂     => fun v b => v = BOOL b
  | nat̂     => fun v m => (v = NAT m) \/ (exists (b : bool), v = BOOL b /\ B_to_N b =-= m)
  | θ ⇥ θ' =>
    (** *Definition 32 *)
    let DenotApproxE (θ : LType) : Expr 0 -> SemType θ _BOT -> Prop :=
        fun e de  => forall sv, de =-= Val sv -> e ∈ ⇑ ↓ (@Ω θ sv (@DenotApproxV θ))
    in fun v f  => exists e, v = FUN e /\
                     forall (w : V 0) (dw : SemType θ),
                       @DenotApproxV θ w dw ->
                       @DenotApproxE θ' (e⎩[w,(λ e)]⎭) (f dw)
  | θ ⨱ θ' => fun v vv => exists v1 v2, v = VPAIR v1 v2 /\
                               @DenotApproxV θ v1 (fst vv) /\
                               @DenotApproxV θ' v2 (snd vv)
  end
.

(* Definition DenotApproxE (θ : LType) : Expr 0 -> SemType θ _BOT -> Prop *)
(*   :=  fun e de => e ∈ ⇑ ↓ (@Ω θ de (@DenotApproxV θ)). *)

(** *Definition 53: Denotational approximation of expressions *)
Definition DenotApproxE (θ : LType) : Expr 0 -> SemType θ _BOT -> Prop :=
  fun e de  => forall sv, de =-= Val sv -> e ∈ ⇑ ↓ (@Ω θ sv (@DenotApproxV θ)).

(** *Notation *)
Notation "v ▷ dv ⦂ θ" := (@DenotApproxV θ v dv)
                             (at level 1, no associativity).
Notation "e ▶ de ⦂ θ" := (@DenotApproxE θ e de)
                             (at level 1, no associativity).

(* Notation "v ▷̅ dv ⦂ θ" := (ideal_closure (@DenotApproxV θ v) dv) *)
(*                              (at level 1, no associativity). *)
(* Notation "e ▶̅ de ⦂ θ" := (ideal_closure (@DenotApproxE θ e) de) *)
(*                              (at level 1, no associativity). *)

Definition DenotApproxCtx (E : Env) (Γ : LCtx E)
  : (Sub E 0) -> SemCtx Γ -> Prop :=
  fun σ η => forall (v : Var E), ((v⎨ v ⎬⎧ σ ⎫) ▷ (lookupV Γ v η) ⦂ (lookupType Γ v))
.

(** *Notation *)
Notation "σ ⊵ η ⦂ Γ" := (@DenotApproxCtx _ Γ σ η)
                     (at level 1, no associativity).


(** *Definition 34: Open logical relations for denotational approximation *)
Definition GenDenotApproxV
           (E : Env) (Γ : LCtx E) (θ : LType) :
  (V E) -> (SemCtx Γ =-> SemType θ) -> Prop :=
  fun v sv => forall σ η, (σ ⊵ η ⦂ Γ) -> ((v ⎧ σ ⎫) ▷ (sv η) ⦂ θ).

Definition GenDenotApproxE
           (E : Env) (Γ : LCtx E) (θ : LType) :
  (Expr E) -> (SemCtx Γ =-> SemType θ _BOT) -> Prop :=
  fun e f  => forall σ η, (σ ⊵ η ⦂ Γ) ->
                             forall sv, f η =-= Val sv ->
              (e ⎩ σ ⎭) ∈ ⇑ ↓ (@Ω θ sv (@DenotApproxV θ))
.

(** *Notation *)
Notation "Γ 'v⊢' v ▷̂̅ dv ⦂ θ" := (ideal_closure (@GenDenotApproxV _ Γ θ v) dv)
                             (at level 201, no associativity).
Notation "Γ 'e⊢' e ▶̂̅ de ⦂ θ" := (ideal_closure (@GenDenotApproxE _ Γ θ e) de)
                             (at level 201, no associativity).

Notation "Γ 'v⊢' v ▷̂ dv ⦂ θ" := (@GenDenotApproxV _ Γ θ v dv)
                             (at level 201, no associativity).
Notation "Γ 'e⊢' e ▶̂ de ⦂ θ" := (@GenDenotApproxE _ Γ θ e de)
                             (at level 201, no associativity).

Lemma Case1 : forall (E : Env) (Γ : LCtx E) (v : Var E),
    (Γ v⊢ (v⎨ v ⎬) ▷̂ (lookupV Γ v) ⦂ (lookupType Γ v)).
Proof.
  intros E Γ v.
  intros σ η H.
  unfold DenotApproxCtx in H.
  apply (H v).
Qed.

Lemma Case1_IC : forall (E : Env) (Γ : LCtx E) (v : Var E),
    (Γ v⊢ (v⎨ v ⎬) ▷̂̅ (lookupV Γ v) ⦂ (lookupType Γ v)).
Proof.
  intros E Γ v.
  apply ideal_closure_sub.
  apply Case1.
Qed.


Definition F θ θ' (E : Env) (Γ : LCtx E)
           (d : SemCtx (θ' × (θ' ⇥ θ) × Γ) =-> SemType θ _BOT) :
  SemCtx Γ -=> ((SemType θ' ⇥ θ) -=> (SemType θ' ⇥ θ))
  := exp_fun (exp_fun d).

Lemma FIXP_Prop : forall (E : Env) θ θ' (Γ : LCtx E)
                    (d : (SemCtx (θ' × (θ' ⇥ θ) × Γ))
                           =-> (SemType θ _BOT))
                    (η : SemCtx Γ) (dw : SemType θ'),
    (ccomp FIXP (F d)) η dw =-= d (η, (ccomp FIXP (F d)) η, dw).
Proof.
  intros E θ θ' Γ d η dw.
  assert ((ccomp FIXP (F d)) η dw =-= (FIXP ((F d) η)) dw). auto.
  rewrite -> H, -> FIXP_eq.
  auto.
Qed.

Lemma fmon_eq_bot : forall (θ θ' : LType) (d d' : SemType θ' ⇥ θ) (a : SemType θ'),
    d =-= d' -> d a =-= ⊥ -> d' a =-= ⊥.
Proof.
  intros θ θ' d d' a H H0.
  rewrite <- H0.
  apply fmon_eq_elim.
  by apply tset_sym.  
Qed.

Lemma ApproxEquivV : forall (θ : LType)  (d d' : SemType θ) (v : V 0),
    d =-= d' -> v ▷ d ⦂ θ -> v ▷ d' ⦂ θ.
Proof.
  intros θ d d' v H H0.
  dependent induction θ.
  - Case "θ = bool".
    simpl in *. rewrite H0. f_equal. apply H.
  - Case "θ = nat".
    simpl in *. destruct H0 as [? | [b [? ?]]].
    left. rewrite H0. f_equal. apply H.
    right. exists b. split. auto. rewrite <- H. auto.
  - Case "θ = θ1 ⇥ θ2".
    inversion H0.
    inversion H1.
    exists x. split. apply H2.
    intros w dw H4.
    specialize (H3 w dw H4).
    unfold "∈", btop, bbot, "∈", Ω in *.
    intros b H6.
    specialize (H3 b).
    apply H3. rewrite <- H6. 
    apply fmon_eq_elim.
    apply H.
  - Case "θ = θ1 ⨱ θ2".
    inversion H0 as [v1 [v2 [eq [? ?]]]].
    exists v1, v2. split. auto. split; simpl; destruct d, d'; simpl in *;
                             apply pairInj_eq in H as [? ?].
    apply IHθ1 with (d:=s). auto. auto.
    apply IHθ2 with (d:=s0). auto. auto.
Qed.

Lemma ApproxEquivE : forall (E : Env) (Γ : LCtx E) (θ : LType)
                       (d d' : SemCtx Γ =-> SemType θ _BOT) (e : Expr E ),
    d =-= d' -> (Γ e⊢ e ▶̂ d ⦂ θ) -> (Γ e⊢ e ▶̂ d' ⦂ θ).
Proof.
  intros E Γ θ d d' e eq H.
  intros σ η σ_A_η ed H'.
  apply fmon_eq_elim with (n:=η) in eq. rewrite <- eq in H'.
  specialize (H σ η σ_A_η ed H'). auto.
Qed.

(* Lemma ApproxEquivV_IC : forall (θ : LType)  (d d' : SemType θ) (v : V 0), *)
(*     d =-= d' -> v ▷̅ d ⦂ θ -> v ▷̅ d' ⦂ θ. *)
(* Proof. *)
(*   intros θ d d' v H H0. *)
(*   intros p sub chain_c down_c. *)
(*   specialize (H0 p sub chain_c down_c). *)
(*   specialize (down_c d' d). *)
(*   apply tset_sym in H. apply Oeq_le in H. *)
(*   apply (down_c H H0). *)
(* Qed. *)

Lemma DenotApproxE_PBot :
  forall (θ θ' : LType) (e : Expr 2), (FUN e) ▷ const (SemType θ) PBot ⦂ (θ ⇥ θ').
Proof.
  intros θ θ' e.
  unfold DenotApproxV.
  exists e. split. auto. intros.
  setoid_replace (Val sv) with (eta sv) in H0.
  apply tset_sym in H0.
  apply PBot_incon_eq with (D:=SemType θ') in H0. contradiction.
  by simpl.
Qed.

Lemma Expand2ApproxCtx :
  forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
    (σ : Sub E 0) (η : SemCtx Γ)
    (v v' : V 0) (dv : SemType θ) (dv' : SemType θ'),
    σ ⊵ η ⦂ Γ -> v ▷ dv ⦂ θ -> v' ▷ dv' ⦂ θ' ->
    (composeSub [v', v] (liftSub (liftSub σ))) ⊵ (η, dv,dv') ⦂ (θ' × θ × Γ).
Proof.
  intros θ θ' E Γ σ η v v' dv dv' H H0 H1.
  unfold DenotApproxCtx.
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
      unfold DenotApproxCtx in H.
      unfold lookupV. simpl.
      rewrite (fst (substComposeSub _)).
      unfold "_ ⎧ _ ⎫".
      rewrite mapVAR. simpl vl.
      do 2 rewrite <-(fst (applyComposeRen _)).
      unfold composeRen.
      simpl. unfold idSub.
      rewrite -> (fst (applyIdMap _ _)).
      unfold DenotApproxCtx in H0.
      specialize (H x).
      apply H.
Qed.

Fixpoint FChainCore (θ θ' : LType) (E : Env) (Γ : LCtx E) (n : natO) :
  (((SemCtx Γ) -=> ((SemType θ' ⇥ θ) -=> (SemType θ' ⇥ θ))) * (SemCtx Γ))
    =-> (SemType θ' ⇥ θ)
  :=
  match n with 
  | 0   => const _ (@const (SemType θ') (SemType θ _BOT) PBot)
  | S m => ev << <| ev, FChainCore θ θ' Γ m |>
  end.

Definition FChain (θ θ' : LType) (E : Env) (Γ : LCtx E) (n : natO) :
  ((SemCtx (θ' × (θ'⇥θ) × Γ)) -=> (SemType θ _BOT)) =->
  ((SemCtx Γ) -=> (SemType θ' ⇥ θ))
     := exp_fun (FChainCore θ θ' Γ n)
      << @CCURRY (SemCtx Γ) (SemType θ' ⇥ θ) (SemType θ' ⇥ θ)
      << @CCURRY (SemCtx Γ * (SemType θ' ⇥ θ)) (SemType θ') (SemType θ _BOT).

Lemma FChainCore_unfold: forall (θ θ' : LType) (E : Env) (Γ : LCtx E) (n : natO),
    FChainCore θ θ' Γ (n.+1) =-= ev << <| ev , FChainCore θ θ' Γ n |> .
Proof. auto. Qed.

Lemma FChainCore_S_unfold: forall (θ θ' : LType) (E : Env) (Γ : LCtx E) (n : natO)
                             (d : (SemCtx Γ -=> (SemType θ' -=> SemType θ _BOT)
                                           -=>
                                           SemType θ' -=> SemType θ _BOT))
                             (η : SemCtx Γ),
    FChainCore θ θ' Γ n (d,η) <= (d η) (FChainCore θ θ' Γ n (d,η)).
Proof.
  intros θ θ' E Γ n d η.
  induction n.
  simpl. apply leastP.
  simpl. apply fmon_le_compat. reflexivity.
  apply IHn.
Qed.
  
Lemma FChainCore_S: forall (θ θ' : LType) (E : Env) (Γ : LCtx E) (n : natO),
    FChainCore θ θ' Γ n <= FChainCore θ θ' Γ (n.+1).
Proof.
  intros θ θ' E Γ n.
  induction n.
  simpl. intro d. apply leastP.
  simpl. intro d. simpl. destruct d.
  simpl. apply fmon_le_compat. reflexivity.
  apply FChainCore_S_unfold.
Qed.  

Lemma FChain_S : forall (θ θ' : LType) (E : Env) (Γ : LCtx E) (n : natO),
  (FChain θ θ' Γ n) <= (FChain θ θ' Γ n.+1).
Proof.
  intros θ θ' E Γ n.
  induction n.
  intros d η a. apply leastP.
  intros d η a. simpl.
  apply fmon_le_compat. reflexivity.
  apply pair_le_compat.  
  apply pair_le_compat. auto.
  apply IHn. auto.
Qed.

Lemma FChainCore_mon (θ θ' : LType) (E : Env) (Γ : LCtx E)
    (d :
       ((SemCtx Γ) -=> ((SemType θ' ⇥ θ) -=> (SemType θ' ⇥ θ))) * (SemCtx Γ)) :
  monotonic (fun (n : natO) => @FChainCore θ θ' E Γ n d).
Proof.
  intros θ θ' E Γ d.
  intros n n' H.
  assert (forall x y, (x <= y)%coq_nat ->
                 FChainCore θ θ' Γ x <= FChainCore θ θ' Γ y).
  intros x y H0.
  induction H0. auto.
  eapply Ole_trans.
  apply IHle. apply FChainCore_S.
  apply H0.
  assert ((n <= n')%coq_nat <-> n <= n').
  apply rwP. apply leP.
  inversion H1. apply H3.
  apply H.
Qed.

Lemma FChain_mon (θ θ' : LType) (E : Env) (Γ : LCtx E)
                 (d : (SemCtx (θ' × (θ'⇥θ) × Γ)) -=> (SemType θ _BOT)):
  monotonic (fun (n : natO) => @FChain θ θ' E Γ n d).
Proof.
  intros θ θ' E Γ d.
  intros n n' H.
  assert (forall m m', (m <= m')%coq_nat -> FChainCore θ θ' Γ m <= FChainCore θ θ' Γ m').
  - Case "Assert".
    intros m m' H0.
    induction H0.
    + SCase "m = m'". auto.
    + SCase "m <= m' ⇒ m <= m'+1".
      eapply Ole_trans.
      apply IHle. apply FChainCore_S.
  simpl.
  apply comp_le_ord_compat.
  apply H0.
  assert ((n <= n')%coq_nat <-> n <= n') by (apply rwP; apply leP).
  apply (snd H1). apply H.
  apply Ole_refl.
Qed.

Definition FC (θ θ' : LType) (E : Env) (Γ : LCtx E)
              (d : (SemCtx (θ' × (θ'⇥θ) × Γ)) -=> (SemType θ _BOT))
  :=
  Eval hnf in mk_fmono (@FChain_mon θ θ' E Γ d).

Lemma FC_simpl :
  forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
    (d : (SemCtx (θ' × (θ'⇥θ) × Γ)) -=> (SemType θ _BOT)) (n : natO),
    FC d n =-= FChain θ θ' Γ n d.
Proof. auto. Qed.

Lemma FC_zero :
  forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
    (d : (SemCtx (θ' × (θ'⇥θ) × Γ)) -=> (SemType θ _BOT)),
    @FC θ θ' E Γ d 0 =-= const _ (@const (SemType θ') (SemType θ _BOT) PBot).
Proof.
  intros θ θ' E Γ d.
  apply fmon_eq_intro.
  intro η. by simpl.
Qed.

Lemma FC_unfold :
  forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
    (d : (SemCtx (θ' × (θ'⇥θ) × Γ)) -=> (SemType θ _BOT)) (n : natO),
    @FC θ θ' E Γ d (n.+1) =-= ev << <| CURRY (CURRY d) , @FC θ θ' E Γ d n |>.
Proof.
  intros θ θ' E Γ d n.
  simpl.
  apply fmon_eq_intro.
  intro η. by simpl.
Qed.

Lemma FC_lub :
  forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
    (d : (SemCtx (θ' × (θ'⇥θ) × Γ)) -=> (SemType θ _BOT)),
    lub (FC d) =-= FixF Γ θ θ' d.
Proof.
  intros θ θ' E Γ d.
  apply fmon_eq_intro. intro η.
  apply fmon_eq_intro. intro a. fold (SemType θ') in a.
  apply lub_eq_compat. simpl. fold (SemType θ). fold (SemType θ').
  apply fmon_eq_intro. intro n.
  generalize a.
  induction n. intro a'.
  simpl. apply tset_refl.
  simpl. intro a'.
  apply fmon_eq_compat. reflexivity.
  apply pair_eq_compat.
  apply pair_eq_compat. auto.
  simpl in IHn. apply fmon_eq_intro. intro a''.
  apply IHn. auto.
Qed.

Lemma Case2 :
  forall (θ θ' : LType) (E : Env) (Γ : LCtx E) (e : Expr E.+2)
    (d : (SemCtx (θ' × (θ' ⇥ θ) × Γ)) =-> SemType θ _BOT),
    ((θ' × (θ' ⇥ θ) × Γ) e⊢ e ▶̂ d ⦂ θ) ->
    forall (n : natO), (Γ v⊢ (λ e) ▷̂ FChain θ θ' Γ n d ⦂ θ' ⇥ θ).
Proof.
  intros θ θ' E Γ e d e_GDA_d n.
  intros σ η σ_DA_η.
  induction n.
  - Case "n = 0".
    simpl.
    exists (e ⎩ liftSub (liftSub σ) ⎭).
    split. auto.
    intros w dw w_DA_dw.
    unfold "∈", btop, bbot, "↓r", Ω.
    intros sv H.
    unfold "∈" in H.
    setoid_replace (Val sv) with (eta sv) in H.
    apply tset_sym in H.
    apply PBot_incon_eq with (D:=SemType θ) in H. contradiction.
      by simpl.
  - Case "n => n+1".
    exists (e ⎩ liftSub (liftSub σ) ⎭).
    split. auto.
    intros w dw w_DA_dw.
    unfold GenDenotApproxE in e_GDA_d.
    rewrite <- (snd (substComposeSub _)).
    intros sv H.
    unfold "∈", btop, bbot, "↓r", Ω.
    intros b H0.
    eapply e_GDA_d.
    apply (Expand2ApproxCtx σ_DA_η IHn w_DA_dw).
    unfold "∈", btop, bbot, "↓r", Ω.
    rewrite -> H. apply tset_refl.
    intros a H2.
    apply H0. auto.
Qed.

Lemma Case2_IC :
  forall (θ θ' : LType) (E : Env) (Γ : LCtx E) (e : Expr E.+2)
    (d : (SemCtx (θ' × (θ' ⇥ θ) × Γ)) =-> SemType θ _BOT),
    ((θ' × (θ' ⇥ θ) × Γ) e⊢ e ▶̂̅ d ⦂ θ) ->
    forall (n : natO), (Γ v⊢ (λ e) ▷̂̅ FC d n ⦂ θ' ⇥ θ).
Proof.
  intros θ θ' E Γ e d e_GDA_d n.
  induction n.
  - Case "n = 0".
    apply ideal_closure_sub.
    intros σ η σ_DA_η.
    simpl.
    exists (e ⎩ liftSub (liftSub σ) ⎭).
    split. auto.
    intros w dw w_DA_dw.
    intros. 
    setoid_replace (Val sv) with (eta sv) in H.
    apply tset_sym in H.
    apply PBot_incon_eq with (D:=SemType θ) in H. contradiction.
      by simpl.
  - Case "n => n+1".
    intros A ss chain_c down_c.
    eapply down_c. apply Oeq_le.
    rewrite FC_simpl. auto.
    apply cont_closed with (f:=(FChain θ θ' Γ n.+1))
                           (P:=GenDenotApproxE e).
    split. apply chain_c. apply down_c.
    intros p H.
    2 : { apply e_GDA_d. }
    apply ss. apply Case2. apply H. 
Qed.

Lemma Case3 : forall (θ : LType) (E : Env) (Γ : LCtx E)
                (v : V E)
                (dv : SemCtx Γ =-> SemType θ),
    (Γ v⊢ v ▷̂ dv ⦂ θ) -> (Γ e⊢ (VAL v) ▶̂ (eta << dv) ⦂ θ).
Proof.
  intros θ E Γ v dv v_DA_dv.
  intros σ η σ_DA_η.
  specialize (v_DA_dv σ η σ_DA_η).
  intros a b fs fs_in.
  unfold "∈", Ω, bbot, "↓r" in fs_in.
  unfold "_ ⎩ _ ⎭". rewrite mapVAL. fold v ⎧ σ ⎫.
  apply fs_in. unfold "∈".
  apply ApproxEquivV with (d:=dv η). apply vinj. apply b.
  apply v_DA_dv.
Qed.

Lemma Case3_IC : forall (θ : LType) (E : Env) (Γ : LCtx E)
                (v : V E)
                (dv : SemCtx Γ =-> SemType θ),
    (Γ v⊢ v ▷̂̅ dv ⦂ θ) -> (Γ e⊢ (VAL v) ▶̂̅ (eta << dv) ⦂ θ).
Proof.
  intros θ E Γ v dv v_DA_dv.
  intros A ss chain_c down_c.
  apply v_DA_dv.
  intros a b.
  specialize (ss (eta << a)).
  apply ss. apply Case3. apply b.
  unfold chain_closed in *.
  intros chs H.
  eapply down_c.
  rewrite -> comp_lub_eq.
  apply Ole_refl.
  apply chain_c.
  simpl. 
  apply H.
  simpl.
  unfold down_closed in *.
  intros d d' H H0.
  eapply down_c.
  2 : { apply H0. }
  apply comp_le_compat. auto. apply H.
Qed.

Lemma Case4 :
  forall (E : Env) (Γ : LCtx E) (op : OrdOp) (e e': Expr E)
    (d d' : SemCtx Γ =-> SemType nat̂ _BOT),
    (Γ e⊢ e ▶̂ d ⦂ nat̂) -> (Γ e⊢ e' ▶̂ d' ⦂ nat̂) ->
    (Γ e⊢ (OOp op e e') ▶̂ (GenBinOpTy (SemOrdOp op) d d') ⦂ bool̂).
Proof.
  intros E Γ op e e' d d' e_DA_d e_DA_d'.
  unfold GenDenotApproxE.
  intros σ η σ_DA_η.
  unfold "_ ⎩ _ ⎭".
  rewrite mapOOp.
  fold e ⎩ σ ⎭ ; fold e' ⎩ σ ⎭.
  unfold "∈", btop.
  intros a b fs H.
  unfold "↓r", "∈", btop, bbot, "∈", "↓r", Ω in *.
  specialize (e_DA_d σ η σ_DA_η).
  specialize (e_DA_d' σ η σ_DA_η).
  eapply antiExec.
  2 : { eapply rt_trans.
        eapply rt_step.
        apply SOOp.
        apply rt_refl.
  }
  simpl in b. unfold id, Smash in b.
  apply kleisliValVal in b. inversion b as [p [eq1 eq2]].
  apply Operator2Val in eq1. inversion eq1 as [n [n' [eq3 [eq4 eq5]]]].
  simpl in *. apply vinj with (D:=SemType bool̂) in eq2.
  apply vinj with (D:=SemType nat̂ * SemType nat̂) in eq5.
  specialize (e_DA_d n eq3).
  specialize (e_DA_d' n' eq4).
  apply e_DA_d.
  intros a' H1.
  unfold "∈", Ω in H1. destruct H1 as [H1 | [b' [? ?]]].
  - Case "d η = NAT n".
    rewrite H1.
    eapply antiExec.
    2 : { eapply rt_trans.
          eapply rt_step.
          apply IOOp.
          apply rt_refl.
    }
    apply e_DA_d'.
    intros a'' H5. destruct H5 as [H5 | [b'' [? ?]]].
    -- SCase "d' η = NAT n'".
       rewrite H5.
       eapply antiExec.
       2 : { eapply rt_trans.
             eapply rt_step.
             apply DOOp.
             apply rt_refl.
       }
       apply H.
       f_equal. destruct p. simpl in eq2.
       apply pairInj_eq in eq5 as [? ?].
       apply discrete_eq in H0. apply discrete_eq in H2.
       rewrite -> H0, -> H2. apply discrete_eq. auto.
    -- SCase "d' η = BOOL b''".
       rewrite H0.
       eapply antiExec.
       2 : { eapply rt_trans.
             eapply rt_trans.
             eapply rt_step.
             apply BoolCast.
             apply rt_refl.
             eapply rt_step.
             apply DOOp.
       }
       apply H.
       f_equal. destruct p. simpl in eq2.
       apply pairInj_eq in eq5 as [? ?].
       rewrite -> H4 in H2.
       apply discrete_eq in H2. rewrite <- H2 in eq2.
       apply discrete_eq in H3.
       rewrite -> H3. apply discrete_eq. rewrite <- eq2.
       destruct b''. auto. auto.
  - Case "d η = BOOL b'".
    rewrite H0.
    eapply antiExec.
    2 : { eapply rt_trans.
          eapply rt_trans.
          eapply rt_step.
          apply BoolCast.
          apply rt_refl.
          eapply rt_step.
          apply IOOp.
    }
    apply e_DA_d'.
    intros a'' H5. destruct H5 as [H5 | [b'' [? ?]]].
    -- SCase "d' η = NAT n'".
       rewrite H5.
       eapply antiExec.
       2 : { eapply rt_trans.
             eapply rt_step.
             apply DOOp.
             apply rt_refl.
       }
       apply H.
       f_equal. destruct p. simpl in eq2.
       apply pairInj_eq in eq5 as [? ?].
       apply discrete_eq in H3. rewrite -> H2 in H1.
       apply discrete_eq in H1. rewrite <- H1 in eq2.
       rewrite -> H3. apply discrete_eq. rewrite <- eq2.
       destruct b'. auto. auto.
    -- SCase "d' η = BOOL b''".
       rewrite H2.
       eapply antiExec.
       2 : { eapply rt_trans.
             eapply rt_trans.
             eapply rt_step.
             apply BoolCast.
             apply rt_refl.
             eapply rt_step.
             apply DOOp.
       }
       apply H.
       f_equal. destruct p. simpl in eq2.
       apply pairInj_eq in eq5 as [? ?].
       rewrite -> H4 in H1.
       rewrite -> H5 in H3.
       apply discrete_eq in H1. rewrite <- H1 in eq2.
       apply discrete_eq in H3. rewrite <- H3 in eq2.
       apply discrete_eq. rewrite <- eq2.
       destruct b'. destruct b''. auto. auto. destruct b''. auto. auto.
Qed.

Lemma Case4_IC :
  forall (E : Env) (Γ : LCtx E) (op : OrdOp) (e e': Expr E)
    (d d' : SemCtx Γ =-> SemType nat̂ _BOT),
    (Γ e⊢ e ▶̂̅ d ⦂ nat̂) -> (Γ e⊢ e' ▶̂̅ d' ⦂ nat̂) ->
    (Γ e⊢ (OOp op e e') ▶̂̅ (GenBinOpTy (SemOrdOp op) d d') ⦂ bool̂).
Proof.
  intros E Γ op e e' d d' e_DA_d e_DA_d'.
  intros A ss chain_c down_c.
  apply cont2_closed with (f:=GenBinOpTy (SemOrdOp op))
                          (P:=GenDenotApproxE (θ:=nat̂) e)
                          (Q:=GenDenotApproxE (θ:=nat̂) e').
  unfold closed. split. apply chain_c. apply down_c.
  intros p q A_p A_q.
  2 : { apply e_DA_d. }
  2 : { apply e_DA_d'. }
  apply ss. apply Case4. apply A_p. apply A_q.
Qed.

Lemma Case5 :
  forall (E : Env) (Γ : LCtx E) (op : BoolOp) (e e': Expr E)
    (d d' : SemCtx Γ =-> SemType bool̂ _BOT),
    (Γ e⊢ e ▶̂ d ⦂ bool̂) -> (Γ e⊢ e' ▶̂ d' ⦂ bool̂) ->
    (Γ e⊢ (BOp op e e') ▶̂ (GenBinOpTy (SemBoolOp op) d d') ⦂ bool̂).
Proof.
  intros E Γ op e e' d d' e_DA_d e_DA_d'.
  unfold GenDenotApproxE.
  intros σ η σ_DA_η.
  unfold "_ ⎩ _ ⎭".
  rewrite mapBOp.
  fold e ⎩ σ ⎭ ; fold e' ⎩ σ ⎭.
  unfold "∈", btop.
  intros a b fs H.
  unfold "↓r", "∈", btop, bbot, "∈", "↓r", Ω in *.
  specialize (e_DA_d σ η σ_DA_η).
  specialize (e_DA_d' σ η σ_DA_η).
  eapply antiExec.
  2 : { eapply rt_trans.
        eapply rt_step.
        apply SBOp.
        apply rt_refl.
  }
  simpl in b. unfold id, Smash in b.
  apply kleisliValVal in b. inversion b as [p [eq1 eq2]].
  apply Operator2Val in eq1. inversion eq1 as [n [n' [eq3 [eq4 eq5]]]].
  simpl in *. apply vinj with (D:=SemType bool̂) in eq2.
  apply vinj with (D:=SemType bool̂ * SemType bool̂) in eq5.
  specialize (e_DA_d n eq3).
  specialize (e_DA_d' n' eq4).
  apply e_DA_d.
  intros a' H1.
  unfold Ω in H1.
  rewrite H1.
  eapply antiExec.
  2 : { eapply rt_trans.
        eapply rt_step.
        apply IBOp.
        apply rt_refl.
  }
  apply e_DA_d'.
  intros a0 H5.
  rewrite H5.
  eapply antiExec.
  2 : { eapply rt_trans.
        eapply rt_step.
        apply DBOp.
        apply rt_refl.
  }
  apply H. simpl.
  f_equal.
  simpl in eq2.
  destruct eq2. inversion H0. clear H0 H2.
  apply f_equal2; inversion eq5; destruct H0, H2; auto.
Qed.

Lemma Case5_IC :
  forall (E : Env) (Γ : LCtx E) (op : BoolOp) (e e': Expr E)
    (d d' : SemCtx Γ =-> SemType bool̂ _BOT),
    (Γ e⊢ e ▶̂̅ d ⦂ bool̂) -> (Γ e⊢ e' ▶̂̅ d' ⦂ bool̂) ->
    (Γ e⊢ (BOp op e e') ▶̂̅ (GenBinOpTy (SemBoolOp op) d d') ⦂ bool̂).
Proof.
  intros E Γ op e e' d d' e_DA_d e_DA_d'.
  intros A ss chain_c down_c.
  apply cont2_closed with (f:=GenBinOpTy (SemBoolOp op))
                          (P:=GenDenotApproxE (θ:=bool̂) e)
                          (Q:=GenDenotApproxE (θ:=bool̂) e').
  unfold closed. split. apply chain_c. apply down_c.
  intros p q A_p A_q.
  2 : { apply e_DA_d. } 2 : { apply e_DA_d'. }
  apply ss. apply Case5. apply A_p. apply A_q.
Qed.

Lemma Case6 :
  forall (E : Env) (Γ : LCtx E) (op : NatOp) (e e': Expr E)
    (d d' : SemCtx Γ =-> SemType nat̂ _BOT),
    (Γ e⊢ e ▶̂ d ⦂ nat̂) -> (Γ e⊢ e' ▶̂ d' ⦂ nat̂) ->
    (Γ e⊢ (NOp op e e') ▶̂ (GenBinOpTy (SemNatOp op) d d') ⦂ nat̂).
Proof.
  intros E Γ op e e' d d' e_DA_d e_DA_d'.
  unfold GenDenotApproxE.
  intros σ η σ_DA_η.
  unfold "_ ⎩ _ ⎭".
  rewrite mapNOp.
  fold e ⎩ σ ⎭ ; fold e' ⎩ σ ⎭.
  unfold "∈", btop.
  intros a b fs H.
  unfold "↓r", "∈", btop, bbot, "∈", "↓r", Ω in *.
  specialize (e_DA_d σ η σ_DA_η).
  specialize (e_DA_d' σ η σ_DA_η).
  eapply antiExec.
  2 : { eapply rt_trans.
        eapply rt_step.
        apply SNOp.
        apply rt_refl.
  }
  simpl in b. unfold id, Smash in b.
  apply kleisliValVal in b. inversion b as [p [eq1 eq2]].
  apply Operator2Val in eq1. inversion eq1 as [n [n' [eq3 [eq4 eq5]]]].
  simpl in *. apply vinj with (D:=SemType nat̂) in eq2.
  apply vinj with (D:=SemType nat̂ * SemType nat̂) in eq5.
  specialize (e_DA_d n eq3).
  specialize (e_DA_d' n' eq4).
  apply e_DA_d.
  intros a' H1.
  unfold Ω in H1. destruct H1 as [H1 | [b' [? ?]]].
  - Case "d η = NAT n".
    rewrite H1.
    eapply antiExec.
    2 : { eapply rt_trans.
          eapply rt_step.
          apply INOp.
          apply rt_refl.
    }
    apply e_DA_d'.
    intros a'' H5. destruct H5 as [H5 | [b'' [? ?]]].
    -- SCase "d' η = NAT n'".
       rewrite H5.
       eapply antiExec.
       2 : { eapply rt_trans.
             eapply rt_step.
             apply DNOp.
             apply rt_refl.
       }
       apply H. left.
       f_equal. destruct p. simpl in eq2.
       apply pairInj_eq in eq5 as [? ?].
       apply discrete_eq in H0. apply discrete_eq in H2.
       rewrite -> H0, -> H2. apply discrete_eq. auto.
    -- SCase "d' η = BOOL b''".
       rewrite H0.
       eapply antiExec.
       2 : { eapply rt_trans.
             eapply rt_trans.
             eapply rt_step.
             apply BoolCast.
             apply rt_refl.
             eapply rt_step.
             apply DNOp.
       }
       apply H. left.
       f_equal. destruct p. simpl in eq2.
       apply pairInj_eq in eq5 as [? ?].
       rewrite -> H4 in H2.
       apply discrete_eq in H2. rewrite <- H2 in eq2.
       apply discrete_eq in H3.
       rewrite -> H3. apply discrete_eq. rewrite <- eq2.
       destruct b''. auto. auto.
  - Case "d η = BOOL b'".
    rewrite H0.
    eapply antiExec.
    2 : { eapply rt_trans.
          eapply rt_trans.
          eapply rt_step.
          apply BoolCast.
          apply rt_refl.
          eapply rt_step.
          apply INOp.
    }
    apply e_DA_d'.
    intros a'' H5. destruct H5 as [H5 | [b'' [? ?]]].
    -- SCase "d' η = NAT n'".
       rewrite H5.
       eapply antiExec.
       2 : { eapply rt_trans.
             eapply rt_step.
             apply DNOp.
             apply rt_refl.
       }
       apply H. left.
       f_equal. destruct p. simpl in eq2.
       apply pairInj_eq in eq5 as [? ?].
       apply discrete_eq in H3. rewrite -> H2 in H1.
       apply discrete_eq in H1. rewrite <- H1 in eq2.
       rewrite -> H3. apply discrete_eq. rewrite <- eq2.
       destruct b'. auto. auto.
    -- SCase "d' η = BOOL b''".
       rewrite H2.
       eapply antiExec.
       2 : { eapply rt_trans.
             eapply rt_trans.
             eapply rt_step.
             apply BoolCast.
             apply rt_refl.
             eapply rt_step.
             apply DNOp.
       }
       apply H. left.
       f_equal. destruct p. simpl in eq2.
       apply pairInj_eq in eq5 as [? ?].
       rewrite -> H4 in H1.
       rewrite -> H5 in H3.
       apply discrete_eq in H1. rewrite <- H1 in eq2.
       apply discrete_eq in H3. rewrite <- H3 in eq2.
       apply discrete_eq. rewrite <- eq2.
       destruct b'. destruct b''. auto. auto. destruct b''. auto. auto.
Qed.

Lemma Case6_IC :
  forall (E : Env) (Γ : LCtx E) (op : NatOp) (e e': Expr E)
    (d d' : SemCtx Γ =-> SemType nat̂ _BOT),
    (Γ e⊢ e ▶̂̅ d ⦂ nat̂) -> (Γ e⊢ e' ▶̂̅ d' ⦂ nat̂) ->
    (Γ e⊢ (NOp op e e') ▶̂̅ (GenBinOpTy (SemNatOp op) d d') ⦂ nat̂).
Proof.
  intros E Γ op e e' d d' e_DA_d e_DA_d'.
  intros A ss chain_c down_c.
  apply cont2_closed with (f:=GenBinOpTy (SemNatOp op))
                          (P:=GenDenotApproxE (θ:=nat̂) e)
                          (Q:=GenDenotApproxE (θ:=nat̂) e').
  unfold closed. split. apply chain_c. apply down_c.
  intros p q A_p A_q.
  2 : { apply e_DA_d. } 2 : { apply e_DA_d'. }
  apply ss. apply Case6. apply A_p. apply A_q.
Qed.

Lemma Case7 : forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
                (e : Expr E) (e' : Expr E.+1)
                (d : SemCtx Γ =-> SemType θ' _BOT)
                (d' : (SemCtx Γ * SemType θ') =-> SemType θ _BOT),
    (Γ e⊢ e ▶̂ d ⦂ θ') -> ((θ' × Γ) e⊢ e' ▶̂ d' ⦂ θ) ->
    (Γ e⊢ (LET e e') ▶̂ (LetTy d' d) ⦂ θ).
Proof.
  intros θ θ' E Γ e e' d d' e_DA_d e_DA_d'.
  unfold GenDenotApproxE; intros σ η σ_DA_η.
  intros a b.
  intros fs fs_in_bbot_Ωlet.
  simpl in b. unfold id, Smash in b.
  apply kleisliValVal in b. inversion b as [η' [eq1 eq2]].
  apply Operator2Val in eq1. inversion eq1 as [η0 [d0 [eq3 [eq4 eq5]]]].
  unfold "↓r", "∈", btop, bbot, "∈", "↓r", Ω in *.
  specialize (e_DA_d σ η σ_DA_η).
  specialize (e_DA_d d0 eq4).
  eapply antiExec.
  2 : { Case "Finding the expression and frame stack.".
        eapply rt_trans.
        eapply rt_step.
        apply SLet.
        apply rt_refl.
  }
  apply e_DA_d.
  intros v v_in_Ωdη. unfold "↓r".
  unfold "↓r", "∈", btop, bbot, "∈", "↓r", Ω in *.
  assert (σ_DA_η' : @DenotApproxCtx E.+1 (θ' × Γ)
                                    (composeSub [v] (liftSub σ)) (η,d0)).
  - Case "Defining the extension of [σ, v] ▷ (η,dv)".
    intro w. dependent destruction w.
    + SCase "w = ZVAR".
      simpl. rewrite -> (fst (substComposeSub _)). unfold "_ ⎧ _ ⎫".
      rewrite -> mapVAR. simpl. rewrite -> mapVAR. simpl. apply v_in_Ωdη.
    + SCase "w = SVAR".
      unfold GenDenotApproxE in e_DA_d'.
      simpl. rewrite -> (fst (substComposeSub _)). unfold "_ ⎧ _ ⎫".
      rewrite -> mapVAR. simpl. unfold renV.
      rewrite <- (fst (applyComposeRen _)).
      unfold composeRen. simpl. unfold idSub.
      rewrite -> (fst (applyIdMap _ _)).
      apply σ_DA_η.
  specialize (e_DA_d' _ _ σ_DA_η').
  apply vinj with (D:=SemCtx Γ * SemType θ') in eq5.
  rewrite <- eq5 in eq2. apply vinj with (D:=SemCtx Γ) in eq3.
  rewrite <- eq3 in eq2.
  specialize (e_DA_d' a eq2).
  specialize (e_DA_d' fs). rewrite -> (snd (substComposeSub _)) in e_DA_d'.
  eapply antiExec.
  2 : { Case "Finding the expression and frame stack.".
        eapply rt_trans.
        eapply rt_step.
        apply Subst.
        apply rt_refl.
  }
  apply e_DA_d'.
  intros v' v'_in_Ωdη.
  apply fs_in_bbot_Ωlet.
  apply v'_in_Ωdη.
Qed.

Lemma Case7_IC : forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
                   (e : Expr E) (e' : Expr E.+1)
                   (d : SemCtx Γ =-> SemType θ' _BOT)
                   (d' : (SemCtx Γ * SemType θ') =-> SemType θ _BOT),
    (Γ e⊢ e ▶̂̅ d ⦂ θ') -> ((θ' × Γ) e⊢ e' ▶̂̅ d' ⦂ θ) ->
    (Γ e⊢ (LET e e') ▶̂̅ (LetTy d' d) ⦂ θ).
Proof.
  intros θ θ' E Γ e e' d d' e_DA_d e_DA_d'.
  intros A ss chain_c down_c.
  apply cont2_closed with (f:=LetTy)
                          (P:=GenDenotApproxE (Γ:=θ' × Γ) e')
                          (Q:=GenDenotApproxE e).
  unfold closed. split. apply chain_c. apply down_c.
  intros p q A_p A_q.
  2 : { apply e_DA_d'. } 2 : { apply e_DA_d. }
  apply ss. apply Case7. apply A_q. apply A_p.
Qed.

Lemma Case8 : forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
                (f v : V E)
                (df : SemCtx Γ =-> SemType (θ' ⇥ θ))
                (dv : SemCtx Γ =-> SemType θ'),
    (Γ v⊢ f ▷̂ df ⦂ θ' ⇥ θ) ->
    (Γ v⊢ v ▷̂ dv ⦂ θ') ->
    (Γ e⊢ (f @ v) ▶̂ (AppTy df dv) ⦂ θ).
Proof.
  intros θ θ' E Γ f v df dv e_DA_df v_DA_dv.
  intros σ η σ_DA_η a b.
  specialize (e_DA_df σ η σ_DA_η).
  specialize (v_DA_dv σ η σ_DA_η).
  destruct e_DA_df as [e [? ?]].
  unfold "_ ⎩ _ ⎭"; rewrite -> mapAPP; fold (f ⎧ σ ⎫) (v ⎧ σ ⎫); rewrite -> H.
  intros fs fs_in.
  unfold "↓r", "∈", btop, bbot, "∈", "↓r", Ω in *.
  eapply antiExec.
  2 : { eapply rt_trans.
        eapply rt_step.
        apply App.
        apply rt_refl.
  }
  specialize (H0 _ _ v_DA_dv a b).
  apply H0. auto.
Qed.

Lemma Case8_IC : forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
                (f v : V E)
                (df : SemCtx Γ =-> SemType (θ' ⇥ θ))
                (dv : SemCtx Γ =-> SemType θ'),
    (Γ v⊢ f ▷̂̅ df ⦂ θ' ⇥ θ) ->
    (Γ v⊢ v ▷̂̅ dv ⦂ θ') ->
    (Γ e⊢ (f @ v) ▶̂̅ (AppTy df dv) ⦂ θ).
Proof.
  intros θ θ' E Γ f v df dv f_DA_df v_DA_dv.
  intros A ss chain_c down_c.
  apply cont2_closed with (f:=AppTy)
                          (P:=GenDenotApproxV (θ:=θ'⇥ θ) f)
                          (Q:=GenDenotApproxV v).
  unfold closed. split. apply chain_c. apply down_c.
  intros p q A_p A_q.
  2 : { apply f_DA_df. } 2 : { apply v_DA_dv. }
  apply ss. apply Case8. apply A_p. apply A_q.
Qed.

Lemma Case9 :
  forall (E : Env) (Γ : LCtx E) (θ : LType) (e0 e1 e2 : Expr E)
    (b : SemCtx Γ =-> SemType bool̂ _BOT)
    (d1 d2 : SemCtx Γ =-> SemType θ _BOT),
    (Γ e⊢ e0 ▶̂ b ⦂ bool̂) -> (Γ e⊢ e1 ▶̂ d1 ⦂ θ) -> (Γ e⊢ e2 ▶̂ d2 ⦂ θ) ->
    (Γ e⊢ IFB e0 e1 e2 ▶̂ (IfBTy b d1 d2) ⦂ θ).
Proof.
  intros E Γ θ e0 e1 e2 b d1 d2 e0_DA_b e1_DA_d1 e2_DA_d2.
  unfold GenDenotApproxE.
  intros σ η σ_DA_η.
  unfold "_ ⎩ _ ⎭".
  rewrite mapIFB.
  fold e0 ⎩ σ ⎭ e1 ⎩ σ ⎭ e2 ⎩ σ ⎭.
  unfold "∈", btop.
  intros a eq fs H.
  unfold "↓r", "∈", btop, bbot, "∈", "↓r", Ω in *.
  specialize (e0_DA_b σ η σ_DA_η).
  specialize (e1_DA_d1 σ η σ_DA_η).
  specialize (e2_DA_d2 σ η σ_DA_η).
  eapply antiExec.
  2 : { eapply rt_trans.
        eapply rt_step.
        apply IfB.
        apply rt_refl.
  }
  simpl in eq. unfold id, Smash in eq.
  apply kleisliValVal in eq. inversion eq as [d1' [eq1 eq2]].
  apply Operator2Val in eq1. inversion eq1 as [d2' [η' [eq3 [eq4 eq5]]]].
  apply kleisliValVal in eq3. inversion eq3 as [p [eq6 eq7]].
  apply Operator2Val in eq6. inversion eq6 as [p' [bv [eq8 [eq9 eq10]]]].
  simpl in *.
  move bv after eq1; move p' after eq1; move p after eq1.
  move η' after eq1; move d2' after eq1. clear eq eq1 eq3 eq6.
  apply vinj with (D:=SemCtx Γ) in eq4.
  apply vinj with (D:=(SemCtx Γ -=> (SemType θ _BOT)) * (SemCtx Γ)) in eq5.
  apply vinj with (D:=SemCtx Γ -=> (SemType θ _BOT)) in eq7.
  apply vinj with (D:=(SemCtx Γ -=> (SemType θ _BOT)) *
                     (SemCtx Γ -=> (SemType θ _BOT))) in eq8.
  apply vinj with (D:=(SemCtx Γ -=> (SemType θ _BOT)) *
                     (SemCtx Γ -=> (SemType θ _BOT)) *
                     bool_cpoType) in eq10.
  assert (IfBCore (fst (fst p)) (snd (fst p)) (snd p) =-= IfBCore d1 d2 bv).
  rewrite <- eq8 in eq10.
  inversion eq10 as [[[? ?] ?] [[? ?] ?]]. simpl in *. rewrite H5.
  destruct bv. simpl. split. apply H3. apply H0.
  simpl. split. apply H4. apply H1.
  rewrite -> H0 in eq7. clear H0.
  rewrite <- eq4 in eq5.
  assert (d2' η =-= Val a).
  rewrite <- eq2. inversion eq5 as [[? ?] [? ?]]. simpl in *.
  split. simpl. apply fmon_le_compat. apply H0. apply H1.
  simpl. apply fmon_le_compat. apply H2. apply H3.
  apply fcont_eq_compat with (B:=SemType θ _BOT) (x0:=η) (y0:=η) in eq7.
  rewrite -> H0 in eq7.
  specialize (e0_DA_b bv eq9).
  apply e0_DA_b.
  intros vb vb_in.
  unfold Ω in vb_in.
  rewrite vb_in.
  destruct bv.
  simpl in eq7.
  specialize (e1_DA_d1 a eq7).
  eapply antiExec.
  2 : { eapply rt_trans.
        eapply rt_step.
        apply IfBT.
        apply rt_refl.
  }
  apply e1_DA_d1.
  intros a' a'_DA_a.
  apply H. apply a'_DA_a.
  simpl in eq7.
  specialize (e2_DA_d2 a eq7).
  eapply antiExec.
  2 : { eapply rt_trans.
        eapply rt_step.
        apply IfBF.
        apply rt_refl.
  }
  apply e2_DA_d2.
  intros a' a'_DA_a.
  apply H. apply a'_DA_a. auto.
Qed.

Lemma Case9_IC :
  forall (E : Env) (Γ : LCtx E) (θ : LType) (e0 e1 e2 : Expr E)
    (b : SemCtx Γ =-> SemType bool̂ _BOT)
    (d1 d2 : SemCtx Γ =-> SemType θ _BOT),
    (Γ e⊢ e0 ▶̂̅ b ⦂ bool̂) -> (Γ e⊢ e1 ▶̂̅ d1 ⦂ θ) -> (Γ e⊢ e2 ▶̂̅ d2 ⦂ θ) ->
    (Γ e⊢ IFB e0 e1 e2 ▶̂̅ (IfBTy b d1 d2) ⦂ θ).
Proof.
  intros E Γ θ e0 e1 e2 b d1 d2 e0_DA_b e1_DA_d1 e2_DA_d2.
  intros A ss chain_c down_c.
  apply cont3_closed with (f:=IfBTy)
                          (P:=GenDenotApproxE (θ:=bool̂) e0)
                          (Q:=GenDenotApproxE (θ:=θ)   e1)
                          (R:=GenDenotApproxE (θ:=θ)   e2).
  unfold closed. split. apply chain_c. apply down_c.
  intros p q r A_p A_q A_r.
  2 : { apply e0_DA_b. } 2 : { apply e1_DA_d1. } 2 : { apply e2_DA_d2. }
  apply ss. apply Case9. apply A_p. apply A_q. apply A_r.
Qed.

Lemma Case10 :
  forall (E : Env) (Γ : LCtx E) (θ θ' : LType) (v v': V E)
    (dv : SemCtx Γ =-> SemType θ)
    (dv' : SemCtx Γ =-> SemType θ'),
    (Γ v⊢ v ▷̂ dv ⦂ θ) -> (Γ v⊢ v' ▷̂ dv' ⦂ θ') ->
    (Γ v⊢ (VPAIR v v') ▷̂ (PairTy dv dv') ⦂ θ ⨱ θ').
Proof.
  intros E Γ θ θ' v v' dv dv' v_DA_dv v'_DA_dv'.
  intros σ η σ_DA_η. simpl.
  unfold "_ ⎧ _ ⎫".
  rewrite -> mapPAIR.
  fold v ⎧ σ ⎫ v' ⎧ σ ⎫.
  exists v ⎧ σ ⎫, v' ⎧ σ ⎫.
  auto.
Qed.

Lemma Case10_IC :
  forall (E : Env) (Γ : LCtx E) (θ θ' : LType) (v v': V E)
    (dv : SemCtx Γ =-> SemType θ)
    (dv' : SemCtx Γ =-> SemType θ'),
    (Γ v⊢ v ▷̂̅ dv ⦂ θ) -> (Γ v⊢ v' ▷̂̅ dv' ⦂ θ') ->
    (Γ v⊢ (VPAIR v v') ▷̂̅ (PairTy dv dv') ⦂ θ ⨱ θ').
Proof.
  intros E Γ θ θ' v v' dv dv' v_DA_dv v'_DA_dv'.
  intros A ss chain_c down_c.
  apply cont2_closed with (f:=PairTy)
                          (P:=GenDenotApproxV (θ:=θ) v)
                          (Q:=GenDenotApproxV (θ:=θ') v').
  unfold closed. split. apply chain_c. apply down_c.
  intros p q A_p A_q.
  apply ss. apply Case10. apply A_p. apply A_q.
  apply v_DA_dv. apply v'_DA_dv'.
Qed.


Lemma Case11 :
  forall (E : Env) (Γ : LCtx E) (θ θ' : LType) (v : V E)
    (dv : SemCtx Γ =-> SemType (θ ⨱ θ')),
    (Γ v⊢ v ▷̂ dv ⦂ θ ⨱ θ') ->
    (Γ e⊢ (EFST v) ▶̂ (FstTy dv) ⦂ θ).
Proof.
  intros E Γ θ θ' v dv v_DA_dv.
  intros σ η σ_DA_η.
  unfold "_ ⎩ _ ⎭".
  rewrite mapFST.
  fold v ⎧ σ ⎫.
  intros a eq fs fs_in.
  specialize (v_DA_dv σ η σ_DA_η).
  destruct v_DA_dv as [v' [v'' [p_eq [? ?]]]].
  rewrite -> p_eq.
  eapply antiExec.
  2 : { eapply rt_trans.
        eapply rt_step.
        apply FstOp.
        apply rt_refl.
  }
  simpl in eq. apply vinj in eq.
  unfold "∈", Ω, bbot, "↓r" in fs_in.
  apply fs_in. unfold "∈".
  apply ApproxEquivV with (d:=fst (dv η)). apply eq.
  apply H.
Qed.

Lemma Case11_IC :
  forall (E : Env) (Γ : LCtx E) (θ θ' : LType) (v : V E)
    (dv : SemCtx Γ =-> SemType (θ ⨱ θ')),
    (Γ v⊢ v ▷̂̅ dv ⦂ θ ⨱ θ') ->
    (Γ e⊢ (EFST v) ▶̂̅ (FstTy dv) ⦂ θ).
Proof.
  intros E Γ θ θ' v dv v_DA_dv.
  intros A ss chain_c down_c.
  apply cont_closed with (f:=FstTy)
                          (P:=GenDenotApproxV (θ:=θ ⨱ θ') v).
  unfold closed. split. apply chain_c. apply down_c.
  intros p A_p.
  apply ss. apply Case11. apply A_p.
  apply v_DA_dv.
Qed.

Lemma Case12 :
  forall (E : Env) (Γ : LCtx E) (θ θ' : LType) (v : V E)
    (dv : SemCtx Γ =-> SemType (θ ⨱ θ')),
    (Γ v⊢ v ▷̂ dv ⦂ θ ⨱ θ') ->
    (Γ e⊢ (ESND v) ▶̂ (SndTy dv) ⦂ θ').
Proof.
  intros E Γ θ θ' v dv v_DA_dv.
  intros σ η σ_DA_η.
  unfold "_ ⎩ _ ⎭".
  rewrite mapSND.
  fold v ⎧ σ ⎫.
  intros a eq fs fs_in.
  specialize (v_DA_dv σ η σ_DA_η).
  destruct v_DA_dv as [v' [v'' [p_eq [? ?]]]].
  rewrite -> p_eq.
  eapply antiExec.
  2 : { eapply rt_trans.
        eapply rt_step.
        apply SndOp.
        apply rt_refl.
  }
  simpl in eq. apply vinj in eq.
  unfold "∈", Ω, bbot, "↓r" in fs_in.
  apply fs_in. unfold "∈".
  apply ApproxEquivV with (d:=snd (dv η)). apply eq.
  apply H0.
Qed.

Lemma Case12_IC :
  forall (E : Env) (Γ : LCtx E) (θ θ' : LType) (v : V E)
    (dv : SemCtx Γ =-> SemType (θ ⨱ θ')),
    (Γ v⊢ v ▷̂̅ dv ⦂ θ ⨱ θ') ->
    (Γ e⊢ (ESND v) ▶̂̅ (SndTy dv) ⦂ θ').
Proof.
  intros E Γ θ θ' v dv v_DA_dv.
  intros A ss chain_c down_c.
  apply cont_closed with (f:=SndTy)
                          (P:=GenDenotApproxV (θ:=θ ⨱ θ') v).
  unfold closed. split. apply chain_c. apply down_c.
  intros p A_p.
  apply ss. apply Case12. apply A_p.
  apply v_DA_dv.
Qed.

Lemma PF_subs_V : forall (θ θ' : LType) (v : V 0) (t : (θ t≤ θ'))
                    (d : SemType θ),
    (v ▷ d ⦂ θ) ->
    (v ▷ (t⟦ t ⟧l) d ⦂ θ').
Proof.
  intros θ θ' v t d H.
  generalize dependent v.
  dependent induction t.
  - Case "bool ≤ nat".
    intros v H. simpl in *. right. exists d. auto.
  - Case "θ ≤ θ".
    auto.
  - Case "θ ≤ θ' ∧ θ' ≤ θ''".
    intros v H. simpl. apply IHt2. apply IHt1. auto.
  - Case "θ0 ⨱ θ1 ≤ θ0' ⨱ θ1'".
    intros v H. destruct H as [pv1 [pv2 [? [? ?]]]].
    exists pv1, pv2. split. auto. split. simpl.
    apply IHt1. auto.
    apply IHt2. auto.
  - Case "θ0 ⇥ θ1 ≤ θ0' ⇥ θ1'".
    intros v H. simpl.
    destruct H as [e [? ?]].
    exists e. split. auto.
    intros w dw H1 sv H2.
    specialize (IHt1 _ _ H1).
    apply kleisliValVal in H2 as [? [? ?]]. unfold id in H2.
    specialize (H0 _ _ IHt1 _ H2).
    intros fs fs_in. apply H0.
    intros a H4. apply fs_in.
    specialize (IHt2 _ _ H4). unfold "∈", Ω.
    apply vinj in H3. eapply ApproxEquivV. apply H3.
    apply IHt2.
Qed.

Lemma PF_subs_E : forall (θ θ' : LType) (e : Expr 0)
                  (t : (θ t≤ θ')) (de : SemType θ _BOT),
    (e ▶ de ⦂ θ) -> (e ▶ (kleisli (eta << t⟦ t ⟧l)) de ⦂ θ').
Proof.
  intros θ θ' e t de H.
  generalize dependent e.
  dependent induction t.
  - Case "bool ≤ nat".
    intros e H d Hd.
    apply kleisliValVal in Hd as [? [? ?]].
    apply vinj in H1. intros fs fs_in.
    specialize (H x H0). apply H. intros v Hv.
    apply PF_subs_V with (θ':=nat̂) (t:=BoolToNatRule) in Hv.
    apply fs_in. apply discrete_eq in H1. destruct Hv as [? | [b [? ?]]].
    left. rewrite <- H1. auto.
    right. exists b. split. auto. rewrite <- H1. auto.
  - Case "θ ≤ θ".
    intros e H d Hd.
    apply kleisliValVal in Hd as [? [? ?]].
    apply vinj in H1.
    specialize (H x H0). intros fs fs_in.
    apply H. intros v Hv. apply fs_in.
    eapply ApproxEquivV. apply H1. auto.
  - Case "θ ≤ θ' ∧ θ' ≤ θ''".
    intros e H d Hd.
    intros fs fs_in.
    specialize (IHt1 _ _ H).
    specialize (IHt2 _ _ IHt1 d).
    simpl in Hd. rewrite -> comp_assoc in Hd.
    rewrite -> kleisli_comp2 in Hd.
    specialize (IHt2 Hd fs fs_in). auto.
  - Case "(θ0,θ1) ≤ (θ0',θ1')".
    intros e H d Hd.
    intros fs fs_in.
    apply kleisliValVal in Hd as [? [? ?]].
    apply vinj in H1.
    specialize (H x H0). apply H.
    intros v Hv. 
    apply fs_in. 
    eapply ApproxEquivV. apply H1.
    apply PF_subs_V. auto.
  - Case "θ0 ⇥ θ1 x y ≤ θ0' ⇥ θ1'".
    intros e H d Hd fs fs_in.
    apply kleisliValVal in Hd as [? [? ?]].
    apply vinj in H1.
    specialize (H x H0). apply H.
    intros v Hv. apply fs_in.
    eapply ApproxEquivV. apply H1.
    apply PF_subs_V. auto.
Qed.

Lemma PF_subs_V' : forall (E : Env) (Γ : LCtx E) (θ θ' : LType)
                     (v : V E) (t : (θ t≤ θ'))
                     (d : SemCtx Γ =-> SemType θ),
    (Γ v⊢ v ▷̂ d ⦂ θ) ->
    (Γ v⊢ v ▷̂ (t⟦ t ⟧l) << d ⦂ θ').
Proof.
  intros E Γ θ θ' v t d H.
  intros σ η σ_DA_η.
  apply PF_subs_V. apply H. auto.
Qed.

Lemma PF_subs_E' : forall (E : Env) (Γ : LCtx E) (θ θ' : LType)
                     (e : Expr E) (t : (θ t≤ θ'))
                     (d : SemCtx Γ =-> SemType θ _BOT),
    (Γ e⊢ e ▶̂ d ⦂ θ) ->
    (Γ e⊢ e ▶̂ kleisli (eta << t⟦ t ⟧l) << d ⦂ θ').
Proof.
  intros E Γ θ θ' v t d H.
  intros σ η σ_DA_η.
  apply PF_subs_E. specialize (H _ _ σ_DA_η).
  intros d' Hd'.
  apply H. auto. 
Qed.

Lemma PF_subs_V_IC : forall (E : Env) (Γ : LCtx E) (θ θ' : LType)
                     (v : V E) (t : (θ t≤ θ'))
                     (d : SemCtx Γ =-> SemType θ),
    (Γ v⊢ v ▷̂̅ d ⦂ θ) ->
    (Γ v⊢ v ▷̂̅ (CCURRY (CCOMP _ _ _)) (t⟦ t ⟧l) d ⦂ θ').
Proof.
  intros E Γ θ θ' v t d H.
  intros A ss chain_c down_c.
  apply cont_closed with (f:= (CCURRY (CCOMP _ _ _)) (t⟦ t ⟧l))
                         (P:=GenDenotApproxV (θ:=θ) v).
  unfold closed. split. apply chain_c. apply down_c.
  intros p A_p.
  2 : { apply H. }
  apply ss. apply PF_subs_V'. apply A_p.
Qed.

Lemma PF_subs_E_IC : forall (E : Env) (Γ : LCtx E) (θ θ' : LType)
                       (e : Expr E) (t : (θ t≤ θ'))
                       (d : SemCtx Γ =-> SemType θ _BOT),
    (Γ e⊢ e ▶̂̅ d ⦂ θ) ->
    (Γ e⊢ e ▶̂̅ (CCURRY (CCOMP _ _ _)) (kleisli (eta << t⟦ t ⟧l)) d ⦂ θ').
Proof.
  intros E Γ θ θ' e t d H.
  intros A ss chain_c down_c.
  apply cont_closed with (f:= (CCURRY (CCOMP _ _ _)) (kleisli (eta << t⟦ t ⟧l)))
                          (P:=GenDenotApproxE (θ:=θ) e).
  unfold closed. split. apply chain_c. apply down_c.
  intros p A_p. 2 : { apply H. }
  apply ss. apply PF_subs_E'. apply A_p.
Qed.
   
(** *Theorem 7: Fundamental Property of Logical Relations *)
Lemma FundamentalPropOfLogicalRelations : forall (E : Env),
    (forall (v : V E) (Γ : LCtx E) (θ : LType) (tj : (Γ v⊢ v ⦂ θ)),
        (Γ v⊢ v ▷̂̅ t⟦ tj ⟧v ⦂ θ))
    /\
    (forall (e : Expr E) (Γ : LCtx E) (θ : LType) (tj : (Γ e⊢ e ⦂ θ)),
        (Γ e⊢ e ▶̂̅ t⟦ tj ⟧e ⦂ θ)).
Proof.
  apply mutual_VE_induction.
  - Case "v = VAR".
    intros E v Γ θ tj.
    dependent induction tj. apply Case1_IC.
    apply PF_subs_V_IC. auto.
  - Case "v = BOOL".
    intros E b Γ θ tj. apply ideal_closure_sub.
    dependent induction tj. simpl.
    intros σ η H. simpl. auto.
    apply PF_subs_V'. auto.
  - Case "v = NAT".
    intros E n Γ θ tj. apply ideal_closure_sub.
    dependent induction tj. simpl.
    intros σ η H. simpl. auto.
    apply PF_subs_V'. auto.
  - Case "v = FUN".
    intros E e IHe Γ θ tj. dependent induction tj.
    intros A ss chain_c down_c.
    eapply down_c. rewrite InSemFun_unfold. rewrite <- FC_lub. auto.
    apply chain_c. intro n. apply Case2_IC with (e:=e).
    apply IHe. apply ss. apply chain_c. apply down_c.
    apply PF_subs_V_IC. auto.
  - Case "v = PAIR".
    intros E v IH v' IH' Γ θ tj.
    dependent induction tj.
    apply Case10_IC. apply IH. apply IH'.
    apply PF_subs_V_IC. auto.
  - Case "e = VAL".
    intros E v IH Γ θ tj.
    dependent induction tj.
    apply Case3_IC. apply IH. simpl.
    apply PF_subs_E_IC. auto.
  - Case "e = APP".
    intros E f IHf v IHv Γ θ tj. dependent induction tj.
    apply Case8_IC. apply IHf. apply IHv.
    apply PF_subs_E_IC. auto.
  - Case "e = OrdOp".
    intros E op e IHe e' IHe' Γ θ tj. dependent induction tj.
    apply Case4_IC. apply IHe. apply IHe'.
    apply PF_subs_E_IC. auto.
  - Case "e = BoolOp".
    intros E op e IHe e' IHe' Γ θ tj. dependent induction tj.
    apply Case5_IC. apply IHe. apply IHe'.
    apply PF_subs_E_IC. auto.
  - Case "e = NatOp".
    intros E op e IHe e' IHe' Γ θ tj. dependent induction tj.
    apply Case6_IC. apply IHe. apply IHe'.
    apply PF_subs_E_IC. auto.
  - Case "e = LET".
    intros E e IHe e' IHe' Γ θ tj. dependent induction tj.
    apply Case7_IC. apply IHe. apply IHe'.
    apply PF_subs_E_IC. auto.
  - Case "e = IFB".
    intros E b IHb e1 IHe1 e2 IHe2 Γ θ tj. dependent induction tj.
    apply Case9_IC. apply IHb. apply IHe1. apply IHe2.
    apply PF_subs_E_IC. auto.
  - Case "e = FST".
    intros E v IH Γ θ tj. dependent induction tj.
    apply Case11_IC. apply IH.
    apply PF_subs_E_IC. auto.
  - Case "e = SND".
    intros E v IH Γ θ tj. dependent induction tj.
    apply Case12_IC. apply IH.
    apply PF_subs_E_IC. auto.
Qed.

End DenoApprox.
