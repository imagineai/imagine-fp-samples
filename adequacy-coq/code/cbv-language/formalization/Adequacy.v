(*begin hide*)

Require Import Utils.
Require Import Program.

(** new in 8.4! *)
Set Automatic Coercions Import.
(** endof new in 8.4 *)

Add LoadPath "../domain-theory".
Add LoadPath "../extended-cbn".

Require Import Rel.
Require Import Biorthogonality.
Require Import Sets.

Require Import Lang.
Require Import Types.

Require Import OperSem.

Require Import domoprs.
Require Import PredomAll.
Require Import Domains.
Require Import DomainStuff.

Include RD.

Require Import DenoApprox.
Require Import OperApprox.
Require Import InSem.
Require Import ExSem.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** *Notations *)
Notation "x ∉ X" := (~ (In _ X x)) (at level 1, no associativity).
Notation "x ∈ X" := (In _ X x) (at level 1, no associativity).
(*end hide*)
(** *)
(*** Chapter 4: ADEQUACY ***)
(** *)



Section Adequacy1_n.
  (*begin hide*)
  Import Relations.Relation_Operators.
  Import DenoApprox.
  Import InSem.
  (*end hide*)
  
Variable n : nat_cpoType.

(** Starting in (fs,e) reduce to n *)
Definition to_n : Rel (Expr 0) FS :=
  fun e fs => (fs, e) ⟼⋆ (∅, ⌊ n ⌋).

Lemma to_const_antiE : AntiexecE to_n.
Proof.
  intros e e' fs fs' H H'.
  unfold to_n in *.
  eapply rt_trans.
  apply H'. apply H.
Qed.

Definition To_n : RelE.
  refine (@mkrelE to_n _).
  eapply to_const_antiE.
Defined.

(** *Notations *)
Notation "'↓r' X" := (DownR X) (at level 1, no associativity).
Notation "↓ X" := (bbot (↓r To_n) X) (at level 1, no associativity).
Notation "⇑ X" := (btop To_n X) (at level 1, no associativity).

Notation "v ▷ dv ⦂ θ" := (@DenotApproxV θ v dv)
                             (at level 1, no associativity).

Notation "v ▷̅ dv ⦂ θ" := (ideal_closure (@DenotApproxV To_n θ v) dv)
                             (at level 1, no associativity).

Notation "σ ⊵ η ⦂ Γ" := (@DenotApproxCtx To_n _ Γ σ η)
                     (at level 1, no associativity).

Notation "Γ 'v⊢' v ▷̂̅ dv ⦂ θ" := (ideal_closure (@GenDenotApproxV To_n _ Γ θ v) dv)
                             (at level 201, no associativity).
Notation "Γ 'e⊢' e ▶̂̅ de ⦂ θ" := (ideal_closure (@GenDenotApproxE To_n _ Γ θ e) de)
                             (at level 201, no associativity).

Notation "Γ 'v⊢' v ▷̂ dv ⦂ θ" := (@GenDenotApproxV To_n _ Γ θ v dv)
                             (at level 201, no associativity).
Notation "Γ 'e⊢' e ▶̂ de ⦂ θ" := (@GenDenotApproxE To_n _ Γ θ e de)
                             (at level 201, no associativity).

Lemma ble : forall (e : Expr 0) (d : SemCtx [] =-> SemType nat̂),
    ([] e⊢ e ▶̂̅ eta << d ⦂ nat̂) ->
    ([] e⊢ e ▶̂ eta << d ⦂ nat̂).
Proof.
  intros e d H.
  intros σ η H0 sv H1. destruct η.  
  assert (σ = idSub 0). apply MapExtensional. intros v. inversion v.
  rewrite -> H2 in *; clear H2.
  assert (AppCpoSet (GenDenotApproxE To_n (Γ:=[]) (θ:=nat̂) e)
                    (@DenotApproxCtx To_n _ [] (idSub 0))
                    (Val sv)
         ).
  apply (@ideal_closure_flat _ _ sv).
  intros. destruct H3 as [? [? ?]]. exists x. exists x0. rewrite <- H2. apply H3.
  apply AppCpoSet_closed. unfold AppCpoSet.
  exists (eta << d). exists (). split; auto. split; auto.
  apply ideal_closure_sub. intros v. inversion v.
  destruct H2 as [d' [ρ [? [? ?]]]]. destruct ρ.
  symmetry in H4.
  specialize (H2 _ _ H3 sv H4).
  apply H2.
Qed.
 
(** *Corollary 6: Adequacy for convergent expressions of type int *)
Lemma Adequacy1_n :
  forall (e : Expr 0) (tj : ([] e⊢ e ⦂ nat̂)),
    t⟦ tj ⟧e () =-= eta n -> (∅, e) ⟼⋆ (∅, ⌊ n ⌋).
Proof.
  intros e tj H. simpl in *.
  assert (AppCpoSet (GenDenotApproxE To_n (θ:=nat̂) e)
                    (@DenotApproxCtx To_n _ [] (idSub 0))
                    (Val n)
         ).
  apply (@ideal_closure_flat _ _ n).
  intros. destruct H1 as [? [? ?]]. exists x. exists x0. rewrite <- H0.
  apply H1.
  assert ([] e⊢ e ▶̂̅ t⟦tj ⟧e ⦂ nat̂).
  apply (snd (FundamentalPropOfLogicalRelations To_n 0)).
  apply AppCpoSet_closed.  
  exists t⟦tj ⟧e. exists (). split. apply H0.
  rewrite H. split. 2 : { auto. }
  apply ideal_closure_sub.
  intros v. inversion v.
  destruct H0 as [? [? [? [? ?]]]].
  specialize (H0 _ _ H1).
  unfold "∈", btop, bbot in *.
  specialize (H0 n (tset_sym H2) ∅).
  unfold "∈", "_ ⎩ _ ⎭", "↓r" in *.
  simpl in *. unfold idSub in *.
  rewrite (snd (applyIdMap _ _)) in H0.
  unfold to_n in *.
  apply H0.
  unfold Ω.
  intros a H3. destruct H3 as [? | [b [? ?]]].
  rewrite -> H3. apply rt_refl.
  rewrite -> H3. apply discrete_eq in H4. rewrite <- H4.
  eapply rt_trans.
  eapply rt_step.
  apply BoolCast. destruct b.
  apply rt_refl. apply rt_refl.
Defined.

End Adequacy1_n.

Section Adequacy1_b.
  (*begin hide*)
  Import Relations.Relation_Operators.
  Import DenoApprox.
  Import InSem.
  (*end hide*)
  
Variable b : bool_cpoType.

(** Starting in (fs,e) reduce to n *)
Definition to_b : Rel (Expr 0) FS :=
  fun e fs => (fs, e) ⟼⋆ (∅,  VAL (BOOL b)).

Lemma to_const_antiE_b : AntiexecE to_b.
Proof.
  intros e e' fs fs' H H'.
  unfold to_n in *.
  eapply rt_trans.
  apply H'. apply H.
Qed.

Definition To_b : RelE.
  refine (@mkrelE to_b _).
  eapply to_const_antiE_b.
Defined.

(** *Notations *)
Notation "'↓r' X" := (DownR X) (at level 1, no associativity).
Notation "↓ X" := (bbot (↓r To_b) X) (at level 1, no associativity).
Notation "⇑ X" := (btop To_b X) (at level 1, no associativity).

Notation "v ▷ dv ⦂ θ" := (@DenotApproxV θ v dv)
                             (at level 1, no associativity).

Notation "v ▷̅ dv ⦂ θ" := (ideal_closure (@DenotApproxV To_b θ v) dv)
                             (at level 1, no associativity).

Notation "σ ⊵ η ⦂ Γ" := (@DenotApproxCtx To_b _ Γ σ η)
                     (at level 1, no associativity).

Notation "Γ 'v⊢' v ▷̂̅ dv ⦂ θ" := (ideal_closure (@GenDenotApproxV To_b _ Γ θ v) dv)
                             (at level 201, no associativity).
Notation "Γ 'e⊢' e ▶̂̅ de ⦂ θ" := (ideal_closure (@GenDenotApproxE To_b _ Γ θ e) de)
                             (at level 201, no associativity).

Notation "Γ 'v⊢' v ▷̂ dv ⦂ θ" := (@GenDenotApproxV To_b _ Γ θ v dv)
                             (at level 201, no associativity).
Notation "Γ 'e⊢' e ▶̂ de ⦂ θ" := (@GenDenotApproxE To_b _ Γ θ e de)
                             (at level 201, no associativity).

(** *Adequacy for convergent expressions of type bool *)
Lemma Adequacy1_b :
  forall (e : Expr 0) (tj : ([] e⊢ e ⦂ bool̂)),
    t⟦ tj ⟧e () =-= eta b -> (∅, e) ⟼⋆ (∅, VAL (BOOL b)).
Proof.
  intros e tj H. simpl in *.

  assert (AppCpoSet (GenDenotApproxE To_b (θ:=bool̂) e)
                    (@DenotApproxCtx To_b _ [] (idSub 0))
                    (Val b)
         ).
  apply (@ideal_closure_flat _ _ b).
  intros. destruct H1 as [? [? ?]]. exists x. exists x0. rewrite <- H0.
  apply H1.

  assert ([] e⊢ e ▶̂̅ t⟦tj ⟧e ⦂ bool̂).
  apply (snd (FundamentalPropOfLogicalRelations To_b 0)).
  
  apply AppCpoSet_closed.
  exists t⟦tj ⟧e. exists (). split. apply H0.
  rewrite H. split. 2 : { auto. }
  apply ideal_closure_sub.
  intros v. inversion v.
  destruct H0 as [? [? [? [? ?]]]].
  specialize (H0 _ _ H1).
  unfold "∈", btop, bbot in *.
  specialize (H0 b (tset_sym H2) ∅).
  unfold "∈", "_ ⎩ _ ⎭", "↓r" in *.
  simpl in *. unfold idSub in *.
  rewrite (snd (applyIdMap _ _)) in H0.
  unfold to_b in *.
  apply H0.
  unfold Ω.
  intros a H3.
  rewrite -> H3. apply rt_refl.
Defined.

End Adequacy1_b.

Section Adequacy2.
  Import Relations.Relation_Operators.
  Import OperApprox.
  Import ExSem.
  
(** Starting in (fs,e) make at least m steps/transitions *)

Definition SemOper_n_steps : iRel (Expr 0) FS := fun n e fs => SemOperStep n (fs,e).

Notation "fse ⟿ n" := (let (fs,e) := fse in SemOper_n_steps n e fs)
                              (at level 1, no associativity).

Definition SemOper_ω_steps (fse : FS * Expr 0) :=
  let (fs,e) := fse in forall n, (fs, e) ⟿ n.

Notation "fse ⇡" := (SemOper_ω_steps fse) (at level 1, no associativity).

Definition SemOper_n_steps_iSet : iSet (Expr 0 * FS) :=
  fun i efs => let (e,fs) := efs in SemOper_n_steps i e fs.

Lemma StepI_SemOper : @StepIndexing.StepI (Expr 0 * FS) (SemOper_n_steps_iSet).
Proof.
  constructor.
  split.
  - Case "Constructor zero".
    intros efs efs_in.
    apply Full_intro.
    intros efs efs_in. destruct efs as [e fs].
    apply Z_Step.
  - Case "Constructor decreasing".
    intros i. induction i.
    + SCase "i = 0".
      intros efs efs_in.
      destruct efs as [e fs].
      apply Z_Step.
    + SCase "i => i+1".
      intros efs efs_in.
      destruct efs as [e fs].
      inversion efs_in.
      eapply S_Step.
      specialize (IHi (e',fs')).
      apply IHi. apply H2.
      apply H3.
Qed.

Lemma AntiE_SemOper : Antiexec_step SemOper_n_steps.
Proof.
  intros e e' fs fs' i fse_i_steps step.
  eapply S_Step. apply fse_i_steps. apply step.
Qed.

Definition n_steps : OperApprox.RelE.
  refine (@mkrel SemOper_n_steps _ _).
  apply StepI_SemOper.
  apply AntiE_SemOper.
Defined.

Notation "'↓r' X" := (DownR X) (at level 1, no associativity).
Notation "↓ X" := (bbot (StepIndexing.mrel (↓r n_steps)) X)
                   (at level 1, no associativity).
Notation "⇑ X" := (btop (StepIndexing.mrel n_steps) X)
                   (at level 1, no associativity).

Notation "v ◁ i | dv ⦂ θ" := (@OperApproxV n_steps θ i v dv)
                              (at level 1, no associativity).

Notation "e ◀ i | de ⦂ θ" := (@OperApproxE n_steps θ i e de)
                             (at level 1, no associativity).

Notation "σ ⊴ i | η ⦂ Γ" := (@OperApproxCtx n_steps _ Γ i σ η)
                             (at level 1, no associativity).

Notation "Γ 'v⊢' v ◁̂ dv ⦂ θ" := (@GenOperApproxV n_steps _ Γ θ v dv)
                                     (at level 201, no associativity).

Notation "Γ 'e⊢' e ◀̂ de ⦂ θ" := (@GenOperApproxE n_steps _ Γ θ e de)
                                     (at level 201, no associativity).

  
(** *Theorem 6: Adequacy for divergent expressions *)
Lemma Adequacy2 :
  forall (e : Expr 0) (θ : LType) (tj : ([] e⊢ e ⦂ θ)),
    ⟦ e ⟧e () =-= ⊥ -> (∅, e) ⇡.
Proof.
  intros e θ tj H.
  intro n.
  unfold SemOper_n_steps.
  assert ([] e⊢ e ◀̂ ⟦e ⟧e ⦂ θ)
    by (apply (snd (OperApprox.FundamentalPropOfLogicalRelations n_steps 0))
       ;auto
       ).
  assert ((idSub 0) ⊴ n | () ⦂ []) by (intro v; inversion v).
  specialize (H0 _ _ _ H1).
  unfold "_ ⎩ _ ⎭", idSub in H0; rewrite (snd (applyIdMap _ _)) in H0.
  apply (OAE_compat H) in H0.
  assert ((n, ∅)
            ∈ (bbot (StepIndexing.mrel (OperApprox.DownR n_steps))
                    (OperApprox.Ω PBot (OperApproxV n_steps θ)))).
  - Case "(n, ∅) ∈ ↑ (Ω ⊥)".
    intros iv iv_in.
    destruct iv as [i v].
    destruct iv_in as [? [? ?]].
    apply tset_sym in H2.
    apply PBot_incon_eq in H2.
    inversion H2.
  specialize (H0 (n,∅) H2).
  simpl in *.
  rewrite Min.min_idempotent in H0.
  apply H0.
Qed.

End Adequacy2.

(* Section Adequacy. *)

Require Import MoT.

Notation "fse ⇡" := (SemOper_ω_steps fse) (at level 1, no associativity).
Variable n : nat.
Variable b : bool.

(** *Corollary 7: Extrinsic adequacy for convergent expressions of type int *)
Theorem Extrinsic_Adequacy1 : forall (e : Expr 0) (tj : ([] e⊢ e ⦂ nat̂)),
    (⟦ e ⟧e () =-= eta (inNat n) -> (∅, e) ⟼⋆ (∅, ⌊ n ⌋)).
Proof.
  intros e tj SemE.
  have H := @In_eq_Ex 0 [] nat̂ () e tj.
  simpl in H. unfold id in H. rewrite -> SemE in H.
  simpl in H. rewrite -> kleisliVal in H.
  do 2 setoid_rewrite SUM_fun_simplx in H.
  apply Adequacy1_n with (tj:=tj). apply (tset_sym H).
Qed.

Theorem Extrinsic_Adequacy1_b : forall (e : Expr 0) (tj : ([] e⊢ e ⦂ bool̂)),
    (⟦ e ⟧e () =-= eta (inNat (B_to_N b)) -> (∅, e) ⟼⋆ (∅, VAL (BOOL b))).
Proof.
  intros e tj SemE.
  have H := @In_eq_Ex 0 [] bool̂ () e tj.
  simpl in H. unfold id in H. rewrite -> SemE in H.
  simpl in H. rewrite -> kleisliVal in H.
  do 2 setoid_rewrite SUM_fun_simplx in H.
  apply Adequacy1_b with (tj:=tj).
  destruct b; apply (tset_sym H).
Qed.

Theorem Extrinsic_Adequacy : forall (e : Expr 0) (tj : ([] e⊢ e ⦂ nat̂)),
    (⟦ e ⟧e () =-= eta (inNat n) -> (∅, e) ⟼⋆ (∅, ⌊ n ⌋))
    /\
    (⟦ e ⟧e () =-= ⊥ -> (∅, e) ⇡)
.
Proof.
  intros e tj.
  split.
  apply (Extrinsic_Adequacy1 tj).
  apply (Adequacy2 (θ:=nat̂) tj).
Qed.

Theorem Intrinsic_Adequacy : forall (e : Expr 0) (tj : ([] e⊢ e ⦂ nat̂)),
    (t⟦ tj ⟧e () =-= eta n -> (∅, e) ⟼⋆ (∅, ⌊ n ⌋))
    /\
    (t⟦ tj ⟧e () =-= ⊥ -> (∅, e) ⇡)
.
Proof.
  intros e tj.
  split.
  apply Adequacy1_n.
  intros SemI.
  have H := @Ex_eq_In () e tj.
  rewrite -> SemI in H.
  rewrite -> kleisli_bot in H.
  apply (Adequacy2 tj) in H.
  apply H.
Qed.

Theorem Extrinsic_Adequacy_b : forall (e : Expr 0) (tj : ([] e⊢ e ⦂ bool̂)),
    (⟦ e ⟧e () =-= eta (inNat (B_to_N b)) -> (∅, e) ⟼⋆ (∅, VAL (BOOL b)))
    /\
    (⟦ e ⟧e () =-= ⊥ -> (∅, e) ⇡)
.
Proof.
  intros e tj.
  split.
  apply (Extrinsic_Adequacy1_b tj).
  apply (Adequacy2 (θ:=bool̂) tj).
Qed.

Theorem Intrinsic_Adequacy_b : forall (e : Expr 0) (tj : ([] e⊢ e ⦂ bool̂)),
    (t⟦ tj ⟧e () =-= eta b -> (∅, e) ⟼⋆ (∅, VAL (BOOL b)))
    /\
    (t⟦ tj ⟧e () =-= ⊥ -> (∅, e) ⇡)
.
Proof.
  intros e tj.
  split.
  apply Adequacy1_b.
  intros SemI.
  have H := @Ex_eq_In_b () e tj.
  rewrite -> SemI in H.
  rewrite -> kleisli_bot in H.
  apply (Adequacy2 tj) in H.
  apply H.
Qed.

Theorem In_Adequacy_1_from_Ex : forall (e : Expr 0) (tj : ([] e⊢ e ⦂ nat̂)),
    (t⟦ tj ⟧e () =-= eta n -> (∅, e) ⟼⋆ (∅, ⌊ n ⌋)).
Proof.
  intros e tj semI.
  have H := @Ex_eq_In () e tj.
  rewrite -> semI in H; simpl in H.
  rewrite -> kleisliVal in H; simpl in H; unfold id in H.
  apply Extrinsic_Adequacy in H. assumption. assumption.
Qed.  

Axiom Intrinsic_Adequacy_2 : forall (θ : LType) (e : Expr 0) (tj : ([] e⊢ e ⦂ θ)),
    (t⟦ tj ⟧e () =-= ⊥ -> (∅, e) ⇡)
.

Theorem Ex_Adequacy_2_from_In : forall (θ : LType) (e : Expr 0) (tj : ([] e⊢ e ⦂ θ)),
    (⟦ e ⟧e () =-= ⊥ -> (∅, e) ⇡).
Proof.
  intros θ e tj semE.
  have H := @In_eq_Ex 0 [] θ () e tj.
  simpl in H; unfold id in H. rewrite -> semE in H.
  rewrite -> kleisli_bot in H; apply tset_sym in H.
  apply Intrinsic_Adequacy_2 in H. assumption. 
Qed.

(* End Adequacy. *)
