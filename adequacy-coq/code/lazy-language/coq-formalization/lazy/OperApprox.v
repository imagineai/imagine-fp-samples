Add Rec LoadPath "." as Top.
Add LoadPath "../denot/domain-theory".
Require Import Utils.

Set Automatic Coercions Import.
Set Implicit Arguments.

Require Import Utf8.
Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Ensembles.
Require Import Biorthogonality.
Require Import Machine.
Require Import Syntax.
Require Import Semantics.
Require Import Compiler.
Require Import Coq.Program.Equality.
Require Import Sets.
Require Import Equalities.
Require Import ZArith.
Require Import BOp.

Add LoadPath "../denot".
Require Import ObsSI.
Require Import StepIndexing.

Require Import domoprs.
Require Import DomainStuff.
Require Import PredomAll.
Require Import uniirec.

Include RD.

From mathcomp Require Import ssreflect.

(** * Realizers, Tests and Main Theorem *)

Module OperApprox (PointerType : UsualDecidableType)
                  (Import Ob : ObservationsSI PointerType).

  Definition RType : Type := Heap * MClos.
  Definition TType : Type := Heap * stack.
  Definition EType : Type := Heap * MEnv.

  Definition iRType : Type := Indexed RType.
  Definition iTType : Type := Indexed TType.

  (** Well-formed realizers *)
  Definition r_wf (r : RType)
    := match r with
         (Γ, (_, η)) => heap_wf Γ /\  Included _ (env_ptr η) (key_set Γ)
       end.

  (** Well-formed tests *)
  Definition t_wf (t : TType)
    := match t with
        (Γ, s) => heap_wf Γ /\ Included _ (stack_ptr s) (key_set Γ)
       end.

  (** Concrete definition of the satisfability relation *)
  Definition isatif (n : nat) (r : RType) (t : TType) : Prop :=
    match r, t with
      (Γ, α), (Δ, s) =>
      r_wf (Γ, α) -> t_wf (Δ, s) ->  Γ ⋈ Δ -> SetIn (Ω n) (Γ ∪ Δ, α, s)
    end.

  Definition satif : iRType -> iTType -> Prop := mrel isatif.

  Module TestRealizer <: TstElt.
    Definition Elt := iRType.
    Definition Tst := iTType.
    Definition satif := satif.
  End TestRealizer.

  Module Import OO := Biorthogonality.Biorthogonality TestRealizer.

  Notation flipIn A x S := (Ensembles.In A S x).

  Reserved Notation "t_Rp( θ , d )" (at level 70, no associativity).
  Infix "∈" := (flipIn _) (at level 80, no associativity).
  Infix "⊆" := (Ensembles.Included _) (at level 80, no associativity).

  Definition LiftRel (θ : type) (d : ty_denot θ)
             (PRel : nat -> t_ty_denot θ -> Ensemble RType) :
    Sets.Power_set (Indexed RType) :=
    fun (iv : nat * RType) =>
      let (i,r) := iv in exists (d' : t_ty_denot θ), d =-= eta d' /\ PRel i d' r
  .
  
  (** Primitive realizers *)
  Fixpoint Primitives (θ : type) (n : nat) : t_ty_denot θ -> Ensemble RType :=
    let R θ n d := fun r => (n, r) ∈ (@LiftRel θ d (Primitives θ)) ⊥ ⊤ in
    match θ with
      tunit => fun _ =>
                let on_iunit f :=
                    fun r => match r with
                          | (Γ, (ival iunit, η)) => f Γ η
                          | _ => False
                          end
                in
                on_iunit (fun Γ η => env_ptr η ⊆ key_set Γ)
    | tint => fun(m : int_cpoType) =>
                let on_iint f :=
                    fun r => match r with
                          | (Γ, (ival (iint z), η)) => f Γ η m z
                          | _ => False
                          end
                in
                on_iint (fun Γ η m z => env_ptr η ⊆ key_set Γ /\ m =-= z)
    | θ1 ⇾ θ2 =>
      fun (f : ty_denot θ1 -=> ty_denot θ2) =>
        let on_igrab f :=
            fun r => match r with
                  | (Γ, (ival (igrab i), η)) => f Γ i η
                  | _ => False
                  end
        in
        let condition Γ i η :=
            forall m d Γ' α β,
              (m < n)%coq_nat ->
              (Γ', α) ∈ R θ1 m d  ->
              r_wf (Γ', α) ->
              Γ ⋈ Γ'  ->
              MClos_to_HClos α = β ->
              forall p, (Γ ∪ Γ') ⋈ ⎨ p ⤇ β ⎬ ->
                   (add p β (Γ ∪ Γ'), (i, p :: η)) ∈ R θ2 m (f d)
        in
        on_igrab (fun Γ i η => env_ptr η ⊆ (key_set Γ) /\ condition Γ i η)
    | θ1 ⨱ θ2 =>
      fun (ab : ty_denot θ1 * ty_denot θ2) =>
      let on_ipair f :=
            fun r => match r with
                  | (Γ, (ival (ipair i i'), η)) => f Γ i i' η
                  | _ => False
                  end
      in
      let condition Γ i i' η := forall m, (m < n)%coq_nat ->
          (Γ, (i, η)) ∈ R θ1 m (fst ab) ∧ (Γ, (i', η)) ∈ R θ2 m (snd ab)
      in
      on_ipair(fun Γ i i' η => env_ptr η ⊆ (key_set Γ) /\ condition Γ i i' η)
    end.
  
  (** General realizers: the orthogonal closure of the primitive realizers *)
  Definition Realizers (θ : type) (n : nat) (d : ty_denot θ) : Ensemble RType
    := fun r => (n, r) ∈ ((@LiftRel θ d (Primitives θ)) ⊥ ⊤).
  Arguments Realizers : clear implicits.
  
  Notation "Rp( θ , n , d )" := (Primitives θ n d)
                                 (at level 70, no associativity).
  Notation "R( θ ,  n , d )" := (Realizers θ n d)
                                 (at level 70, no associativity).
  
  (** Tests *)
  Definition Tests (θ : type) (d : ty_denot θ) : Ensemble iTType
    := (@LiftRel θ d (Primitives θ)) ⊥.
  Arguments Tests : clear implicits.

  Add Parametric Morphism n α s : (fun Γ => SetIn (Ω n) (Γ, α, s)) with
      signature Equal ==> iff as inΩ_heap_mor.
  Proof.
    intros Γ Γ' EQ.
    split.
    eapply eq_closed.
    split ; auto.
    eapply eq_closed.
    split ; auto.
    symmetry.
    auto.
  Qed.

  Lemma tests_realizers:
    forall θ (d : ty_denot θ),
      Same_set _ (Tests θ d) ((@LiftRel θ d (Primitives θ)) ⊥ ⊤ ⊥).
  Proof.
    intros θ d.
    change (Same_set _ (Tests θ d)
                     ((bbot ∘ btop ∘ bbot) (@LiftRel θ d (Primitives θ)))).
    rewrite GF.comp_equality.
    unfold f.
    unfold Tests.
    reflexivity.
  Qed.

  Lemma realizer_in_Ω :
    forall n Γ Δ α s a (d : ty_denot a),
      r_wf (Γ, α)
      -> t_wf (Δ, s)
      -> Γ ⋈ Δ
      -> (Γ, α) ∈ R(a, n, d)
      -> SetIn (Tests _ d) (n, (Δ, s))
      -> SetIn (Ω n) (Γ ∪ Δ, α, s).
  Proof.
    intros n Γ Δ α s a d wf1 wf2 J0 R0 H0.
    specialize (R0 (n, (Δ,s)) H0).
    simpl in R0. rewrite -> Nat.min_id in R0.
    eapply R0 ; auto.
  Qed.

  Lemma Tests_Equal' :
    forall a d d', d =-= d' ->
              Same_set _ (LiftRel d (Primitives a) ⊥)
                       (LiftRel d'(Primitives a) ⊥).
  Proof.
    intros a d d' d_eq_d'.
    split. intros (n,t) Ht (m, r) Hr. unfold LiftRel, "∈" in *.
    apply Ht. unfold "∈" in *. destruct Hr. exists x. rewrite -> d_eq_d'. auto.
    intros (n,t) Ht (m, r) Hr. unfold LiftRel, "∈" in *.
    apply Ht. unfold "∈" in *. destruct Hr. exists x. rewrite <- d_eq_d'. auto.
  Qed.
  
  Lemma primitive_Equal:
    forall n Γ α a d d', d =-= d' ->
                  SetIn (Rp(a,n,d)) (Γ, α) ->
                  SetIn (Rp(a,n,d')) (Γ, α).
  Proof.
    intros n Γ α a d d' d_eq_d' pr.
    simpl in *. unfold SetIn, "∈" in *. destruct α as [c η]. destruct a.
    destruct c ; try contradiction.
    destruct v ; try contradiction.
    apply pr.
    destruct c ; try contradiction.
    destruct v ; try contradiction.
    simpl. rewrite <- d_eq_d'.
    apply pr.
    destruct c ; try contradiction.
    destruct v ; try contradiction.
    simpl. split. apply pr. intros m d0 Γ' α β m_le_n H H0 H1 H2 p H3.
    unfold "∈". intros d'0 H4.
    have bla := fcont_eq_compat d_eq_d' (tset_refl d0).
    have ble := Tests_Equal' bla. apply ble in H4.
    destruct pr.
    specialize (H6 m d0 Γ' α β m_le_n H H0 H1 H2 p H3 d'0 H4).
    auto.
    destruct c ; try contradiction.
    destruct v ; try contradiction.
    split. apply pr. intros m m_le_n.
    split. intros d'0 H. apply (snd pr). auto.
    have bla := fcont_eq_compat (tset_refl (FST (ty_denot a1) (ty_denot a2)))
                               d_eq_d'. simpl in bla.
    have ble := Tests_Equal' bla. apply ble in H. auto.
    intros d'0 H. apply (snd pr). auto.
    have bla := fcont_eq_compat (tset_refl (SND (ty_denot a1) (ty_denot a2)))
                               d_eq_d'. simpl in bla.
    have ble := Tests_Equal' bla. apply ble in H. auto.
  Qed.

  Lemma primitive_realizer:
    forall n Γ α a (d : t_ty_denot a),
      SetIn (Primitives a n d) (Γ, α) ->
      SetIn (Realizers a n (eta d)) (Γ, α).
  Proof.
    intros n Γ α a d.
    intros r_in (m,d') d'test.
    specialize (d'test (n, (Γ, α))). apply d'test.
    unfold LiftRel, "∈". exists d. auto.
  Qed.

  Lemma Tests_Equal:
    forall n Γ Δ s a d, Γ ≃ Δ ->
                 SetIn (Tests a d) (n, (Γ, s)) ->
                 SetIn (Tests a d) (n, (Δ, s)).
  Proof.
    intros n Γ Δ s a d EQ I.
    intros (m, (Γ',(c,η))) r_in. simpl.
    intros H H0 H1.
    assert (Γ' ∪ Δ ≃ Γ' ∪ Γ) as EQ'.
    eapply Equal_join_mor.
    auto.
    reflexivity.
    symmetry.
    auto.
    pattern (Γ' ∪ Δ). rewrite -> EQ'.
    specialize (I (m, (Γ', (c, η))) r_in). apply I.
    auto. 
    split.
    rewrite EQ.
    apply H0.
    rewrite EQ.
    apply H0.
    rewrite EQ.
    auto.
  Qed.
  
  Add Parametric Morphism n a (d : ty_denot a) α :
    (fun Γ => SetIn (Tests a d) (n, (Γ, α))) with
      signature Equal ==> iff as tests_heap_mor.
  Proof.
    intros Γ Δ EQ.
    split ;
      eapply Tests_Equal ;
      eauto.
    symmetry.
    auto.
  Qed.

  Lemma primitive_StepI : forall (θ : type) (Γ : Heap) (α : MClos)
                            (d : t_ty_denot θ) (i : nat),
      (Γ,α) ∈ Rp(θ, i.+1, d) -> (Γ,α) ∈ Rp(θ, i, d).
  Proof.
    intros θ Γ (c,η) d i H.
    destruct θ.
    - Case "θ = tunit". auto.
    - Case "θ = tint". auto.
    - Case "θ = θ1 ⇾ θ2".
      unfold "∈" in *.
      destruct c ; try contradiction.
      destruct v ; try contradiction. split. apply H.
      intros m d0 Γ' α β H0 H1 H2 H3 H4 p H5. eapply (snd H).
      apply Lt.lt_S. auto. apply H1. auto. auto. auto. auto.
    - Case "θ = θ1 ⨱ θ2".
      unfold "∈" in *.
      destruct c ; try contradiction.
      destruct v ; try contradiction. split. apply H.
      intros m H0. apply (snd H). apply Lt.lt_S. auto. 
  Qed.

  Lemma test_StepI : forall (θ : type) (Δ : Heap) (s : stack)
                       (d : ty_denot θ) (i : nat),
      SetIn (Tests θ d) (i.+1, (Δ, s)) ->
      SetIn (Tests θ d) (i, (Δ, s)).
  Proof.
    intros θ Δ s d i Δs_in.
    intros (j, (Γ, (c, η))) r_in. simpl.
    specialize (Δs_in (j,(Γ, (c, η))) r_in).
    have H0 := Min.min_spec i j. destruct H0 as [[? ?] | [? ?]].
    intros rwf twf Γ_Δ. specialize (Δs_in rwf twf Γ_Δ).
    rewrite Nat.min_comm.
    rewrite -> H0. apply Lt.lt_le_S in H.
    apply Min.min_l in H. rewrite Nat.min_comm in H. rewrite -> H in Δs_in.
    apply (decreasing stepI i). auto.
    intros rwf twf Γ_Δ. specialize (Δs_in rwf twf Γ_Δ).
    rewrite Nat.min_comm. rewrite -> H0.
    have j_leq_Si := Nat.le_trans _ _ _ H (Le.le_n_Sn i).
    have j_min_Si := Min.min_r (i.+1) j j_leq_Si.
    rewrite Nat.min_comm in j_min_Si.
    rewrite -> j_min_Si in Δs_in. auto.
  Qed.

  Lemma test_gen_StepI : forall (θ : type) (Δ : Heap) (s : stack)
                           (d : ty_denot θ) (i j : nat),
      (j <= i)%coq_nat ->
      SetIn (Tests θ d) (i, (Δ, s)) ->
      SetIn (Tests θ d) (j, (Δ, s)).
  Proof.
    intros θ Γ α d i j j_leq_i H.
    induction i.
    - Case "i = 0".
      inversion j_leq_i. auto.
    - Case "i = i.+1".
      apply Nat.le_succ_r in j_leq_i.
      destruct j_leq_i as [j_leq_i | j_eq_i].
      apply IHi. auto. apply test_StepI. auto.
      rewrite j_eq_i. auto.
  Qed.

  Lemma realizer_StepI :  forall (θ : type) (Γ : Heap) (α : MClos)
                            (d : ty_denot θ) (i : nat),
      (Γ,α) ∈ R(θ, i.+1, d) -> (Γ,α) ∈ R(θ, i, d).
  Proof.
    intros θ Γ (c,η) d i H.
    intros (j,(Δ,s)) jΔs_in rwf twf Γ_Δ.
    specialize (H (j,(Δ,s)) jΔs_in rwf twf Γ_Δ).
    have H0 := Min.min_spec i j. destruct H0 as [[? ?] | [? ?]].
    rewrite -> H1. apply Lt.lt_le_S in H0.
    apply Min.min_l in H0. rewrite -> H0 in H.
    apply (decreasing stepI i). auto.
    rewrite -> H1.
    have j_leq_Si := Nat.le_trans _ _ _ H0 (Le.le_n_Sn i).
    have j_min_Si := Min.min_r (i.+1) j j_leq_Si.
    rewrite -> j_min_Si in H. auto.
  Qed.

  Lemma primitive_gen_StepI : forall (θ : type) (Γ : Heap) (α : MClos)
                                (d : t_ty_denot θ) (i j : nat),
      (j <= i)%coq_nat -> (Γ,α) ∈ Rp(θ, i, d) -> (Γ,α) ∈ Rp(θ, j, d).
  Proof.
    intros θ Γ α d i j j_leq_i H.
    induction i.
    - Case "i = 0".
      inversion j_leq_i. auto.
    - Case "i = i.+1".
      apply Nat.le_succ_r in j_leq_i.
      destruct j_leq_i as [j_leq_i | j_eq_i].
      apply IHi. auto. apply primitive_StepI. auto.
      rewrite j_eq_i. auto.
  Qed.

  (* Notation "Γα ◁ n | d" := (SetIn (Primitives _ n d) Γα) *)
  (*                           (at level 80, no associativity). *)

  (* Notation "Γα ◀ n | d" := (SetIn (Realizers _ n d) Γα) *)
  (*                           (at level 80, no associativity). *)

  Lemma realizer_gen_StepI : forall (θ : type) (Γ : Heap) (α : MClos)
                               (d : ty_denot θ) (i j : nat),
      (j <= i)%coq_nat -> (Γ,α) ∈ R(θ,i,d) -> (Γ,α) ∈ R(θ,j,d).
  Proof.
    intros θ Γ α d i j j_leq_i H.
    induction i.
    - Case "i = 0".
      inversion j_leq_i. auto.
    - Case "i = i.+1".
      apply Nat.le_succ_r in j_leq_i.
      destruct j_leq_i as [j_leq_i | j_eq_i].
      apply IHi. auto. apply realizer_StepI. auto.
      rewrite j_eq_i. auto.
  Qed.
  
  Fixpoint EnvRealizers (n : nat) (ctx : ctx) : ctx_denot ctx -> Ensemble EType :=
    match ctx return ctx_denot ctx -> Ensemble EType with
      nil => fun _ => fun er =>
                    match er with
                      (Γ, nil) => True
                    | _ => False
                    end
    | a :: ctx => fun ρ => fun er =>
                         let (d, ρ') := ρ in
                         match er with
                           (Γ, p :: η) =>
                           SetIn (EnvRealizers n ctx ρ') (Γ, η) /\
                           exists α β, find p Γ = Some β /\
                                  HClos_to_MClos β = Some α /\
                                SetIn (Realizers a n d) (Γ, α)
                         | _ => False
                         end
    end.

  Notation "g ⊴ n | p" := (SetIn (EnvRealizers n _ p) g)
                            (at level 80, no associativity).

  Definition GRealizers (c : ctx) (a : type)
             (d : ctx_denot c =-> ty_denot a) : Ensemble Code
    := fun i => forall (n : nat) (Γ : Heap) (η : MEnv) (ρ : ctx_denot c),
          heap_wf Γ -> (Γ, η) ⊴ n | ρ -> (Γ,(i, η)) ∈ R(a,n,d ρ)
  .
  
  Notation "π '⊢' i '◀|' d" := (@GRealizers π _ d i)
                              (at level 201, no associativity).

  Definition exists_fresh_pointer := forall Γ η s, exists p, fresh_for p Γ η s.
    
  Lemma isatif_down_closed : forall (r : RType) (t : TType) (i j : nat),
      (j <= i)%coq_nat -> isatif i r t -> isatif j r t.
  Proof.
    intros (Γ,α) (Δ,s) i.
    induction i; intros j j_leq_i H.
    - Case "i = 0".
      inversion j_leq_i. auto.
    - Case "i => i+1".
      apply Lt.le_lt_or_eq in j_leq_i.
      destruct j_leq_i as [j_le_Si | j_eq_Si].
      apply Lt.lt_le_S in j_le_Si.
      apply Le.le_S_n in j_le_Si.
      apply IHi. auto. intros rwf twf Γ_Δ.
      apply (decreasing stepI i).
      apply H; auto.
      rewrite -> j_eq_Si. auto.
  Qed.
  
  Lemma bbot_down_closed : forall (θ : type) (d : ty_denot θ) (t : TType) (i j : nat),
      (j <= i)%coq_nat -> (i, t) ∈ Tests θ d -> (j, t) ∈ Tests θ d.
  Proof.
    intros θ d (Δ,s) i j j_leq_i t_in.
    intros (i',r) ir_in.
    specialize (t_in (i',r) ir_in) as satif.
    apply Nat.min_le_compat_l with (p:=i') in j_leq_i.
    eapply isatif_down_closed.
    apply j_leq_i. auto.
  Qed.

  Lemma tests_bot : forall (n : nat) (θ : type) (Γ : Heap),
      SetIn (Tests θ PBot) (n, (Γ, nil)).
  Proof.
    intros n θ Γ.
    intros (m, r) LiftRp. destruct LiftRp as [? [? _]].
    symmetry in H. apply PBot_incon_eq in H.
    contradiction.
  Qed.
 
  Lemma var_to_nat_lookup:
    forall ctx a,
    forall v : var ctx a,
    forall ρ : ctx_denot ctx,
    forall Q : nth_error ctx (var_to_nat v) = Some a,
      lookup v ρ = lookup_nat _ _ Q ρ.
  Proof.
    induction v.
    intros ρ Q.
    simpl.
    dependent destruction Q.
    auto.
    intros ρ Q.
    destruct ρ as [d ρ'].
    simpl. simpl in Q.
    unfold compose.
    simpl.
    eauto.
  Qed.

  Lemma env_realizer_lookup:
    forall n Γ η ctx (ρ : ctx_denot ctx) a (i : nat),
    forall Q : nth_error ctx n = Some a,
      (Γ, η) ⊴ i | ρ -> 
      exists p, nth_error η n = Some p /\
           exists α β, find p Γ = Some β
                  /\ HClos_to_MClos β = Some α
                  /\ (Γ, α) ∈ R(a,i, lookup_nat _ _ Q ρ).
  Proof.
    induction n ;
    intros Γ η ctx ρ a i Q Hr0.
    - simpl in Q.
      destruct ctx as [ | a' ctx'].
      discriminate.
      injection Q. intro. subst.
      destruct ρ as [d ρ'].
      destruct η as [ | p  η'].
      contradiction.
      destruct Hr0 as [Her1 [α [β [F0 [? Hr2]]]]].
      exists p.
      split. simpl. auto.
      exists α, β.
      split ; auto.
      dependent destruction Q.
      simpl. auto.
    - simpl in Q. 
      destruct ctx as [ | a' ctx'].
      discriminate.
      destruct ρ as [d ρ'].
      destruct η as [ | p  η'].
      contradiction.
      simpl.    
      eapply IHn.
      eapply Hr0.
  Qed.

  Lemma isatif_eq_Fullset : forall (r : RType) (t : TType), isatif 0 r t.
  Proof.
    intros (Γ,α) (Δ,s) Γwf Δwf Γ_Δ.
    apply (zero stepI).
    apply Full_intro.
  Qed.

  Lemma r_wf_find:
    forall Γ p α β,
      heap_wf Γ ->
      Map.find p Γ = Some β ->
      HClos_to_MClos β = Some α ->
      r_wf (Γ, α).
  Proof.
    intros Γ p β.
    intros Hwf Hf.
    destruct β as [he η].
    split. auto.
    transitivity (heap_range_ptr Γ).
    eapply find_heap_range. destruct Hwf; destruct e.
    inversion H0. rewrite -> H. inversion H0. eauto.
    transitivity (heap_ptr Γ).
    unfold heap_ptr.
    auto with sets.
    unfold heap_ptr.
    eapply Hf.
  Qed.
  Lemma r_wf_heap:
    forall Γ α, r_wf (Γ, α) -> heap_wf Γ.
  Proof.
    intros Γ α H.
    destruct α.
    eapply H.
  Qed.

  Lemma r_wf_heap':
    forall Γ he η, r_wf (Γ, (he, η)) -> heap_wf Γ.
  Proof.
    intros Γ he η H.
    eapply H.
  Qed.

  Lemma r_wf_joinable:
    forall Γ p α β,
      MClos_to_HClos α = β ->
      Γ ⋈ ⎨ p ⤇ β ⎬ ->
      r_wf (Γ, α) ->
      heap_wf (Γ ∪ ⎨ p ⤇ β ⎬).
  Proof.
    intros Γ p α β αHclos Hjble H.
    unfold heap_wf.
    rewrite Join_heap_ptr ; auto.
    rewrite Join_key_set ; auto.
    unfold heap_ptr at 2.
    destruct α as [i η]. cbv in αHclos. rewrite <- αHclos.
    rewrite key_set_singleton.
    rewrite heap_range_singleton.
    rewrite <- Union_assoc.
    set (H' := r_wf_heap _ _ H).
    unfold heap_wf in H'.
    rewrite H'.
    rewrite Union_comm.
    rewrite Union_subset.
    reflexivity.
    transitivity (key_set Γ).
    eapply H.
    eapply Included_Union_1.
    auto. auto.
  Qed.

  Lemma t_wf_heap:
    forall Γ s, t_wf (Γ, s) -> heap_wf Γ.
  Proof.
    intros Γ s H.
    eapply H.
  Qed.

  Hint Resolve r_wf_heap r_wf_heap' t_wf_heap.

  Ltac pattern_heap_conf :=
    match goal with
      [ |- SetIn _ (?Γ, _, _) ] => pattern Γ
    end.
  
  Ltac pattern_heap_realizer :=
    match goal with
      [ |- SetIn _ (?Γ, _) ] => pattern Γ
    end.

  Ltac pattern_heap_test :=
    match goal with
      [ |- SetIn _ (_, (?Γ, _)) ] => pattern Γ
    end.

  Ltac pattern_satif :=
    match goal with
      [ |- (_, (?Γ, _)) ⊧ _ ] => pattern Γ
    end.

  Ltac heap_rewrite_conf H := pattern_heap_conf ; rewrite -> H.
  Ltac heap_rewrite_realizer H := pattern_heap_realizer ; rewrite -> H.
  Ltac heap_rewrite_test H := pattern_heap_test ; rewrite -> H.
  Ltac rewrite_satif H := pattern_satif ; rewrite -> H.
  
  Lemma satif_Equal1:
    ∀ (n : nat) (Γ Δ : t elt_pair) (c : Code) (η : MEnv) 
      (m : nat) (Δ' : Heap) (s' : stack),
      Γ ≃ Δ -> (n, (Γ, (c, η))) ⊧ (m, (Δ', s'))
      → (n, (Δ, (c, η))) ⊧ (m, (Δ', s')).
  Proof.
    intros n Γ Δ c η m Δ' s' Γ_eq_Δ H.
    intros rwf twf Δ_Δ'.
    apply eq_closed with (w:=(Γ ∪ Δ', (c, η), s')).
    split. apply Equal_join_mor. rewrite -> Γ_eq_Δ. auto. auto.
    apply F.Equal_refl. auto. apply H. split; rewrite -> Γ_eq_Δ; apply rwf.
    auto. rewrite -> Γ_eq_Δ. auto.
  Qed.

  Add Parametric Morphism n α ts :
    (fun Γ => (n, (Γ, α)) ⊧ ts) with
      signature Equal ==> iff as satif_equal1.
  Proof.
    intros Γ Δ H.
    split; intros H0; destruct ts as [m [Δ' s]]; destruct α as [c η];
    eapply satif_Equal1. apply H; auto.
    auto. symmetry. apply H. auto.
  Qed.
   
  Lemma realizers_Equal:
    forall n Γ Δ α a d, Γ ≃ Δ ->
                   SetIn (Realizers a n d) (Γ, α) ->
                   SetIn (Realizers a n d) (Δ, α).
  Proof.
    intros n Γ Δ (c, η) a d Γ_eq_Δ H (m, (Δ', s')) its_in.
    specialize (H (m, (Δ', s')) its_in).
    symmetry in Γ_eq_Δ.
    rewrite_satif Γ_eq_Δ. auto.
  Qed.

  Lemma realizers_Equal':
    forall i Γ α a d d', d =-= d' ->
                 SetIn (Realizers a i d) (Γ, α) ->
                 SetIn (Realizers a i d') (Γ, α).
  Proof.
    intros i Γ (c, η) a d d' d_eq_d' H (j, (Δ, s)) its_in.
    apply H. apply Tests_Equal' with (d':=d'). auto. auto.
  Qed.

  Add Parametric Morphism n a (d : ty_denot a) α :
    (fun Γ => SetIn (Realizers a n d) (Γ, α)) with
      signature Equal ==> iff as realizer_heap_mor.
  Proof.
    intros Γ Δ EQ.
    split ;
    eapply realizers_Equal ;
    auto.
    symmetry.
    auto.
  Qed.  
  
  Lemma env_realizers_Equal:
    forall c n η ρ Γ Δ , Γ ≃ Δ ->
                    SetIn (EnvRealizers n c ρ) (Γ, η) ->
                    SetIn (EnvRealizers n c ρ) (Δ, η).
  Proof.
    induction c.
    intros n η ρ Γ Δ EQ Her0.
    destruct ρ.
    destruct η ; try contradiction.
    auto.
    intros n η ρ Γ Δ EQ Her1.
    destruct ρ as [d ρ'].
    destruct η as [ | q η'] ; try contradiction.
    destruct Her1 as [H0 [α [β [F [β_to_α G]]]]].
    split.
    eapply IHc.
    eauto.
    auto.
    exists α, β.
    split.
    eapply find_Equal ; eauto. split. auto.
    pattern Δ. rewrite <- EQ.
    auto.
  Qed.

  Add Parametric Morphism n c (ρ : ctx_denot c) η :
    (fun Γ => SetIn (EnvRealizers n c ρ) (Γ, η)) with
      signature Equal ==> iff as env_realizer_heap_mor.
  Proof.
    intros Γ Γ' EQ.
    split ;
      eapply env_realizers_Equal ;
      eauto.
    symmetry.
    auto.
  Qed.

  Lemma realizer_extend_heap:
    forall n Γ Δ α a (d : ty_denot a),
      r_wf (Γ, α) -> Γ ⋈ Δ -> (Γ, α) ∈ R(a, n, d) -> (Γ ∪ Δ, α) ∈ R(a, n, d).
  Proof.
    intros n Γ Δ α a d Hwf Hjble H0.
    eapply btop_weakened.
    - Case "Down Closed".
      intros fs m m' H m_le_m'. eapply bbot_down_closed. apply m_le_m'. apply H.
    - Case "Proof".
      intros (m, (Δ', s)) ts_in.
      intros m_le_n Hwf1 Hwf2 Hjble2.
      assert (Γ ∪ Δ ∪ Δ' ≃ Γ ∪ Δ' ∪ Δ) as Eq1.
      destruct_join_joinable.
      repeat rewrite Join_assoc_1 ; eauto.
      eapply Equal_join_mor ; eauto.
      reflexivity.
      heap_rewrite_conf Eq1.
      destruct_join_joinable.
      eapply extend_heap ; auto.
      assert (conf_wf (Γ ∪ Δ', α, s)) as H.
      destruct α as [i η].
      split.
      eapply wf_union ; eauto.
      split.
      rewrite Join_key_set.
      transitivity (key_set Γ).
      eapply Hwf.
      auto with sets.
      auto.
      rewrite Join_key_set.
      transitivity (key_set Δ').
      eapply Hwf2.
      auto with sets.
      auto.
      auto.
      eapply realizer_in_Ω with (d:=d) ; auto.
      apply realizer_gen_StepI with (i:=n). auto. auto.
  Qed.

  Lemma env_realizer_nil:
    forall n Γ η (ρ : ctx_denot nil), (Γ, η) ⊴n| ρ -> η = nil.
  Proof.
    intros n Γ η ρ H.
    simpl in H.
    destruct η.
    auto.
    contradict H.
  Qed.

  Lemma env_realizer_def:
    forall (n : nat) (c : ctx) Γ η (ρ : ctx_denot c) α β a (d : ty_denot a) q,
      find q Γ = Some β ->
      HClos_to_MClos β = Some α ->
      (Γ, α) ∈ R(a , n , d) -> 
      (Γ, η) ⊴n| ρ  ->
      (Γ, q :: η) ⊴n| ((d, ρ) : ctx_denot (a :: c)).
  Proof.
    intros n c Γ η ρ α β a d q F H Hr Henv.
    split. auto.
    exists α, β. split ; auto.
  Qed.

  Lemma env_realizer_StepI :  forall (c : ctx) (Γ : Heap) (η : MEnv)
                                (ρ : ctx_denot c) (i : nat),
      (Γ, η) ⊴ i.+1 | ρ -> (Γ, η) ⊴ i | ρ.
  Proof.
    dependent induction c;
    intros Γ η ρ i H. destruct ρ; auto.
    destruct ρ; destruct η; auto.
    destruct H as [? [α [β [? [? ?]]]]].
    apply env_realizer_def with (α:=α) (β:=β). auto. auto.
    apply realizer_StepI. auto. apply IHc. auto.
  Qed.

  Lemma env_realizer_gen_StepI :  forall (c : ctx) (Γ : Heap) (η : MEnv)
                                    (ρ : ctx_denot c) (i j : nat),
      (j <= i)%coq_nat -> (Γ, η) ⊴ i | ρ -> (Γ, η) ⊴ j | ρ.
  Proof.
    intros c Γ α ρ i j j_leq_i H.
    induction i.
    - Case "i = 0".
      inversion j_leq_i. auto.
    - Case "i = i.+1".
      apply Nat.le_succ_r in j_leq_i.
      destruct j_leq_i as [j_leq_i | j_eq_i].
      apply IHi. auto. apply env_realizer_StepI. auto.
      rewrite j_eq_i. auto.
  Qed.
  
  Lemma ble : forall (n : nat) (Γ : Heap) (η : MEnv) (c : ctx) (z : Z),
      (Γ,((ival (iint z)), η)) ∈ R(tint,n,eta z).
  Proof.
    intros n Γ η c z.
    eapply btop_weakened.
    - Case "Down Closed".
      intros fs m m' H m_le_m'. eapply bbot_down_closed. apply m_le_m'. apply H. 
    - Case "Proof".
      intros (m,(Δ,s)) mt_test. simpl. intros H [H0 H0'] H1 H2.
      unfold bbot, LiftRel, "∈" in mt_test.
      specialize (mt_test (m,(Γ, (ival (iint z), η)))). simpl in mt_test.
      rewrite -> Nat.min_id in mt_test.
      apply mt_test. exists z; auto. auto. auto. auto.
  Qed.
   
  Lemma env_realizer_extend_heap: forall (c : ctx) (n : nat) Γ Δ η (ρ : ctx_denot c),
      heap_wf Γ -> Γ ⋈ Δ -> (Γ, η) ⊴n| ρ -> (Γ ∪ Δ, η) ⊴n| ρ.
  Proof.
    induction c.
    - intros n Γ Δ η ρ wf H1 H2.
      destruct ρ.
      set (Q := env_realizer_nil _ _ _ _ H2).
      clearbody Q.
      rewrite Q in H2.
      rewrite Q.
      auto.
    - intros n Γ Δ η ρ wf H1 H2.
      destruct ρ as [d ρ'].
      destruct η as [ | q η'].
      contradict H2.
      destruct H2 as [Q1 Q2].
      destruct Q2 as [α [β [Eq [Q4 Q5]]] Q6].
      eapply env_realizer_def.
      assert (find q (Γ ∪ Δ) = Some β) as F0.
      eapply find_submap.
      eapply join_sub1 ; auto.
      auto.
      exact F0. apply Q4.
      eapply realizer_extend_heap.
      eapply r_wf_find ; eauto.
      auto. 
      auto. auto.
  Qed.

  Lemma env_realizer_realizer_cons:
    forall (n : nat) (Γ Γ' : Heap) (α : MClos) (β : HClos)
      (a : type) (d : ty_denot a) (c : ctx) (ρ : ctx_denot c) (η : MEnv)
      (q : key),
      heap_wf Γ ->
      HClos_to_MClos β = Some α ->
      r_wf (Γ', α) ->
      Γ ⋈ Γ' ->
      (Γ ∪ Γ') ⋈ ⎨ q ⤇ β ⎬ ->
      (Γ, η) ⊴n| ρ ->
      (Γ',α) ∈ R(a,n,d) ->
      (Γ ∪ Γ' ∪ ⎨ q ⤇ β ⎬, q :: η) ⊴ n | ((d, ρ) : ctx_denot (a :: c)).
  Proof.
    intros n Γ Γ' α β a d c ρ η q Hwf0 β_to_α Hwf1 Hjble0 Hjble1 Her0 Hr0.
    split.
    - heap_rewrite_realizer (Join_assoc_1) ;
      destruct_join_joinable ;
      auto.
      apply env_realizer_extend_heap ; eauto.
    - exists α, β.
      split.
      -- eapply find_Joinable_singleton_1. auto.
      -- assert (Γ ∪ Γ' ∪ (⎨ q ⤇ β ⎬) ≃ Γ' ∪ (Γ ∪ ⎨ q ⤇ β ⎬)) as E.
         destruct_join_joinable.
         rewrite <- Join_assoc_1 ; eauto.    
         eapply Equal_join_mor ; eauto.
         reflexivity.
         split. auto.
         heap_rewrite_realizer E.
         destruct_join_joinable.
         eapply realizer_extend_heap ;
         auto.
  Qed.
  
  Lemma compiler_correctness_unit :
    forall (c : ctx) (d : ctx_denot c =-> t_ty_denot tunit),
      (c ⊢ (ival iunit) ◀| (eta << d)).
  Proof.
    intros c d n Γ η ρ Γwf ρ_approx.
    eapply btop_weakened.
    - Case "Down Closed".
      intros fs m m' H m_le_m'. eapply bbot_down_closed. apply m_le_m'. apply H.
    - Case "Proof".
      intros (m,(Δ,s)) mt_test. simpl. intros H [H0 H0'] H1 H2.
      specialize (mt_test (m,(Γ,(ival iunit,η)))). simpl in mt_test.
      rewrite -> Nat.min_id in mt_test.
      apply mt_test. exists (d ρ). split; auto. auto. auto. auto.
  Qed.

  Lemma compiler_correctness_int : forall (c : ctx) (z : Z),
      @GRealizers c tint (eta << const _ z) (ival (iint z)).
  Proof.
    intros c z n Γ η ρ Γwf ρ_approx.
    eapply btop_weakened.
    - Case "Down Closed".
      intros fs m m' H m_le_m'. eapply bbot_down_closed. apply m_le_m'. apply H. 
    - Case "Proof".
      intros (m,(Δ,s)) mt_test. simpl. intros H [H0 H0'] H1 H2.
      specialize (mt_test (m,(Γ,(ival (iint z),η)))). simpl in mt_test.
      rewrite -> Nat.min_id in mt_test.
      apply mt_test. exists z. split. auto. auto. auto. auto. auto.
  Qed.

  Lemma realizer_access:
    forall Γ η ctx a (ρ : ctx_denot ctx) n (i : nat) (Q : nth_error ctx n = Some a),
      heap_wf Γ -> (Γ, η) ⊴ i | ρ ->
                               (Γ, (iaccess n, η)) ∈ R(a,i, lookup_nat _ _ Q ρ).
  Proof.
    intros Γ η ctx a ρ n i Q Γwf ρ_approx.
    set (d := lookup_nat n ctx Q ρ).
    eapply btop_weakened.
    - Case "Down Closed".
      intros fs m m' H m_le_m'. eapply bbot_down_closed. apply m_le_m'. apply H. 
    - Case "Proof".
      intros (j, (Δ, s)) t_in.
      intros j_leq_i.
      destruct j. apply isatif_eq_Fullset.
      intros Hwf1 Hwf2 Γ_Δ.
      set (H := env_realizer_lookup _ _ _ _ _ i Q ρ_approx).
      clearbody H.
      destruct H  as [p [EQ EX]].
      destruct EX as [α [β [F1 [? Hr2]]]].
      eapply antiex. econstructor.
      exact EQ.
      assert (find p (Γ ∪ Δ) = Some β) as E.
      eapply find_submap ; auto.
      eapply join_sub1 ; auto.
      auto.
      apply E. apply H.
      eapply add_marker.
      assert (find p (Γ ∪ Δ) = Some β) as E.
      eapply find_submap ; auto.
      eapply join_sub1 ; auto.
      auto.
      apply E. auto.
      eapply realizer_in_Ω.
      eapply r_wf_find.
      auto.
      eauto.
      auto.
      auto. auto.
      apply realizer_gen_StepI with (i:=i). apply le_Sn_le. auto.
      apply Hr2.
      apply test_StepI. auto.
  Qed.

  Lemma compiler_correctness_var :forall (θ : type) (c : ctx) (v : var c θ), 
      @GRealizers c θ (lookup v) (iaccess (var_to_nat v)).
  Proof.
    intros θ c v n Γ η ρ Γwf ρ_approx.
    simpl.
    set (Q := nth_var_to_nat v).
    clearbody Q.
    rewrite (var_to_nat_lookup v ρ Q).
    apply realizer_access ; auto.
  Qed.      

  Lemma env_realizer_ptr:
    forall n ctx (ρ : ctx_denot ctx) η Γ, heap_wf Γ -> (Γ, η) ⊴ n | ρ ->
                                     Included _ (env_ptr η) (key_set Γ).
  Proof.
    induction ctx ;
    intros ρ η Γ Hwf0 Her0.
    destruct ρ.
    destruct η.
    firstorder.
    contradiction.
    destruct ρ as [d ρ'].
    destruct η ; try contradiction.
    eapply env_ptr_cons_included.
    eapply IHctx ; eauto.
    eapply Her0.
    destruct Her0 as [Her1 [α [β [F0 [β_to_α Hr1]]]]].
    eapply key_set_find_in.
    apply F0.
  Qed.
  
  Lemma compiler_correctness_abs:
    ∀ (θ1 θ2 : type) (c : ctx) (d : ctx_denot (θ1 :: c) =-> ty_denot θ2)
      (i : Code),
      @GRealizers (θ1 :: c) θ2 d i ->
      @GRealizers c (θ1 ⇾ θ2) (AbsTy d) (ival (igrab i)).
  Proof.
    intros θ1 θ2 c d i IH.
    intros n Γ η ρ Γwf ρ_approx.
    apply primitive_realizer. split.
    eapply env_realizer_ptr ; eauto. fold ctx_denot; simpl; unfold id.
    intros m d' Γ' α β m_le_n Hp0 Hwf1 Hjble β_to_α p Hjble1.
    set (Γ'' := Γ ∪ Γ' ∪ ⎨ p ⤇ β ⎬).
    assert ((Γ'', p :: η) ⊴ m | ((d', ρ) : ctx_denot (θ1 :: c))) as He1.
    - Case "Assert".
      eapply env_realizer_realizer_cons. auto.
      apply HClos_prop'. apply β_to_α.
      auto. auto. auto.
      apply env_realizer_gen_StepI with (i:=n). apply Nat.lt_le_incl.
      auto. auto.
      apply Hp0.
    eapply IH.
    assert (Γ ⋈ ⎨ p ⤇ β ⎬) as H1.
    destruct_join_joinable. auto.
    assert (Γ' ⋈ ⎨ p ⤇ β ⎬) as H2.
    destruct_join_joinable. auto.
    rewrite <- Join_add ; eauto.
    rewrite Join_assoc_1 ; eauto.
    eapply wf_union ; eauto.
    eapply r_wf_joinable ; eauto.
    assert (add p β (Γ ∪ Γ') ≃ Γ'') as E.
    unfold Γ''.
    symmetry.
    eapply Join_add. auto.
    heap_rewrite_realizer E.
    auto.
  Qed.

  Lemma realizer_rec : forall (θ : type) (π : ctx)
                         (d : ctx_denot (θ :: π) =-> ty_denot θ) (i : Code),
      exists_fresh_pointer ->
      (θ :: π ⊢ i ◀| d) ->
      (π ⊢ (irec i) ◀| (FixF d)).
  Proof.
    intros θ π d i EFP IH.
    intro n. induction n; intros Γ η ρ Γwf ρ_approx.
    - Case "i = 0".
      intros (m,ts) ts_in. apply isatif_eq_Fullset.
    - Case "i => i+1".
      eapply btop_weakened.
      -- SCase "Down Closed".
         intros fs m m' H m_le_m'. eapply bbot_down_closed.
         apply m_le_m'. apply H.
      -- SCase "Proof".
         intros (m,(Δ,s)) ts_in m_leq_Sn. destruct m. apply isatif_eq_Fullset.
         intros Γαwf Δwf Γ_Δ.
         destruct EFP with (Γ:=Γ ∪ Δ) (η:=η) (s:=s) as [p p_fresh].
         eapply antiex. constructor. apply p_fresh.
         assert (Map.add p (C (irec i), η) (Γ ∪ Δ)
                         ≃
                 Map.add p (C (irec i), η) Γ ∪ Δ).
         symmetry.
         eapply heap_add_prop''. destruct p_fresh. auto. auto.
         heap_rewrite_conf H. clear H.
         destruct p_fresh. apply fresh_for_heap_join in H.
         assert (extended_ρ : SetIn (EnvRealizers m (θ :: π) ((FixF d) ρ, ρ))
                                    (Map.add p (C (irec i), η) Γ, p :: η)
                ).
         --- SSCase "Assert extended env realizer".
             assert (Γ ∪ (⎨ p ⤇ (C (irec i), η) ⎬) ≃
                       Map.add p (C (irec i), η) Γ).
             ---- SSSCase "assert".
                  rewrite <- (Join_add (Joinable_fresh (fst H))). reflexivity.
             eapply env_realizer_def. apply F.add_eq_o. auto.
             unfold HClos_to_MClos. simpl. reflexivity.
             eapply realizers_Equal. apply H1.
             apply realizer_extend_heap. auto. apply Joinable_fresh.
             apply (fst H).
             apply realizer_gen_StepI with (i:=n). apply le_S_n. auto.
             apply IHn. auto.
             apply env_realizer_StepI. auto.
             eapply env_realizers_Equal. apply H1.
             eapply env_realizer_extend_heap. auto.
             apply Joinable_fresh. apply (fst H).
             apply env_realizer_gen_StepI with (i:=n.+1).
             apply le_Sn_le. auto. auto.
         assert (extended_Γwf : heap_wf (Map.add p (C (irec i), η) Γ)).
         --- SSCase "Assert extended heap well-formed".
             apply wf_add. auto. apply Γαwf.
             specialize (IH m (Map.add p (C (irec i), η) Γ) (p::η)
                            ((FixF d) ρ, ρ) extended_Γwf extended_ρ (m,(Δ,s))).
         unfold "_ ⊧ _", satif, mrel, isatif in IH.
         rewrite -> Nat.min_id in IH.
         apply IH.
         assert ((FixF d) ρ =-= d ((FixF d) ρ, ρ)).
         simpl. fold ctx_denot. eapply tset_trans. rewrite -> fixp_eq. simpl.
         unfold id. auto. auto.
         eapply Tests_Equal'. symmetry. apply H1.
         apply test_StepI. auto. split. auto.
         eapply env_realizer_ptr. auto. apply extended_ρ. auto.
         apply Join_add_prop'. apply H. auto. auto.
  Qed.

  Lemma compiler_correctness_let :
    exists_fresh_pointer ->
    ∀ (π : ctx) (θ1 θ2 : type)
      (d : ctx_denot (θ1 :: π) =-> ty_denot θ1)
      (d' : ctx_denot (θ1 :: π) =-> ty_denot θ2)
      (i i' : Code),
      (θ1 :: π ⊢ i ◀| d) ->
      (θ1 :: π ⊢ i' ◀| d') ->
      (π ⊢ (ilet (irec i) i') ◀| LetTy d' (FixF d)).
  Proof.
    intros EFP c θ1 θ2 d d' i i' IHt_1 IHt_2.
    intros n Γ η ρ Γwf ρ_approx.
    eapply btop_weakened.
    - Case "Down Closed".
      intros fs m m' H m_le_m'. eapply bbot_down_closed. apply m_le_m'. apply H.
    - Case "Proof".
      intros (m, (Δ, s)) t_in m_leq_n.
      destruct EFP with (Γ:=Γ ∪ Δ) (η:=η) (s:=s) as [p p_fresh].
      destruct m. apply isatif_eq_Fullset.
      intros Γwf' Δwf Γ_Δ.
      eapply antiex. constructor. apply p_fresh.
      apply realizer_rec in IHt_1. 2:{ auto. }
      destruct p_fresh. apply fresh_for_heap_join in H.
      -- assert (Γ ∪ (⎨ p ⤇ (C (irec i), η) ⎬)
                   ≃
                 Map.add p (C (irec i), η) Γ).
       rewrite <- (Join_add (Joinable_fresh (fst H))). reflexivity.
      -- assert (extended_ρ : SetIn (EnvRealizers m (θ1 :: c) ((FixF d) ρ, ρ))
                                    (add p (C (irec i), η) Γ, p :: η)
                ).
         eapply env_realizer_def. apply F.add_eq_o. auto. reflexivity.
         unfold snd. eapply realizers_Equal. apply H1.
         apply realizer_extend_heap. auto. apply Joinable_fresh. apply (fst H).
         apply IHt_1. auto. apply env_realizer_gen_StepI with (i:=n).
         apply le_Sn_le. auto. auto.
         eapply env_realizers_Equal. apply H1.
         eapply env_realizer_extend_heap. auto.
         apply Joinable_fresh. apply (fst H).
         apply env_realizer_gen_StepI with (i:=n).
         apply le_Sn_le. auto. auto.
      -- assert (Map.add p (C (irec i), η) (Γ ∪ Δ)
                         ≃
                 Map.add p (C (irec i), η) Γ ∪ Δ).
         symmetry. eapply heap_add_prop''. apply fresh_for_heap_join_1.
         auto. auto. auto.
      heap_rewrite_conf H2. clear H2.
      -- assert (extended_Γwf : heap_wf (Map.add p (C (irec i), η) Γ)).
         apply wf_add. auto. apply Γwf'.
      specialize (IHt_2 m (Map.add p (C (irec i), η) Γ) (p :: η) ((FixF d) ρ, ρ)
                        extended_Γwf extended_ρ (m,(Δ,s))).
      unfold "_ ⊧ _", satif, mrel, isatif in IHt_2.
      rewrite -> Nat.min_id in IHt_2.
      apply IHt_2.
      apply test_StepI. auto. split. auto.
      eapply env_realizer_ptr. auto. apply extended_ρ. auto.
      apply Join_add_prop'. apply H. auto. auto.
  Qed.

  Lemma tests_functional:
    forall n Γ Δ α β s a b (d : ty_denot a) (f : ty_denot (a ⇾ b)) p,
      HClos_to_MClos β = Some α ->
      r_wf (Γ, α) ->
      t_wf (Δ, s) ->
      Γ ⋈ Δ ->
      (Γ ∪ Δ) ⋈ ⎨ p ⤇ β ⎬ ->
      (Γ, α) ∈ R(a, n, d) -> 
      SetIn (Tests b (AppTy_ρ f d)) (n, (Δ, s)) ->
      SetIn (Tests (a ⇾ b) f) (n ,(Γ ∪ Δ ∪ ⎨ p ⤇ β ⎬, ⌑ p :: s)).
  Proof.
    intros n Γ Δ α β s a b d f p.
    intros β_to_α Hwf0 Hwf1 Hjble0 Hjble1 Hr0 Ht0.
    eapply bbot_weakened.
    - Case "Down Closed".
      intros (Γ',α') m' m'' H m'_le_m''. destruct H as [f' [? ?]].
      exists f'. split. auto.
      change ((Rp( a ⇾ b, m'', f')) (Γ', α')) with
          ((Γ', α') ∈ (Rp( a ⇾ b, m'', f'))).
      apply primitive_gen_StepI with (i:=m'). auto. auto.
    - Case "Proof".
      intros (m', (Γ'', α')) r_in m'_leq_m.
      set (Γ' := Γ ∪ Δ ∪ (⎨ p ⤇ β ⎬)).
      destruct m'. apply isatif_eq_Fullset.
      intros rwf twf Γ''compat.
      destruct r_in as [f' [? ?]].
      destruct α' as [c η].
      destruct c ; try contradiction.
      destruct v ; try contradiction.
      eapply antiex. constructor.
      destruct H0 as [Hinc0 Hgrab].
      assert (Γ'' ⋈ Γ) as Hjble3.
      destruct_join_joinable.
      rewrite joinable_comm.
      eapply Joinable_submap.
      rewrite joinable_comm.
      eauto.
      unfold Γ'.
      rewrite Join_assoc_1 ; auto.
      eapply join_sub1 ; auto.
      assert (Γ'' ∪ Γ ⋈ ⎨ p ⤇ β ⎬) as Hjble4.
      destruct_join_joinable.
      rewrite joinable_comm.
      eapply Joinable_join_intro_r.
      eapply Joinable_submap.
      rewrite joinable_comm.
      eapply Γ''compat ; auto.
      unfold Γ'.
      eapply join_sub2 ; auto.
      rewrite joinable_comm ; auto.
      apply HClos_prop in β_to_α.
      have m'_leq_n := Nat.le_trans m' (m'.+1) n
                                   (Nat.lt_le_incl m' (m'.+1)
                                                    (Nat.lt_succ_diag_r m'))
                                   m'_leq_m.
      have Hr0m' := realizer_gen_StepI m'_leq_n Hr0.
      specialize (Hgrab m' d Γ α β (Nat.lt_succ_diag_r m') Hr0m' Hwf0
                        Hjble3 β_to_α p Hjble4).
      set (Δ' := Γ'' ∪ Γ ∪ (⎨ p ⤇ β ⎬)).
      assert (Γ'' ⋈ Δ) as E0.
      unfold Γ' in *.
      repeat destruct_join_joinable.
      rewrite -> Join_comm_1 in Γ''compat.
      rewrite <- Join_assoc_1 in Γ''compat ; auto.
      rewrite -> joinable_comm in Γ''compat ; auto.
      rewrite joinable_comm.
      eapply Joinable_join_elim_2.
      assert (⎨ p ⤇ β ⎬ ∪ Γ ⋈ Δ) as E'.
      rewrite joinable_comm ; auto.
      exact E'.
      auto.
      rewrite joinable_comm ; auto.
      assert (Γ'' ∪ Γ' ≃  Δ' ∪ Δ) as E.
      unfold Γ' in *. unfold Δ' in *.
      repeat destruct_join_joinable.
      symmetry.
      repeat rewrite Join_assoc_1  ; auto.
      eapply Equal_join_mor ; auto.
      reflexivity.
      repeat rewrite Join_assoc_1 ; auto.
      eapply Equal_join_mor ; auto.
      reflexivity.
      heap_rewrite_conf E.
      apply realizer_in_Ω with (d := ((AppTy_ρ f) d)).
      destruct_join_joinable.
      assert (Γ'' ⋈ ⎨ p ⤇ β ⎬) as Hjble5.
      auto.
      assert (Γ ⋈ ⎨ p ⤇ β ⎬) as Hjble6.
      auto.
      assert (Same_set _ (key_set (⎨ p ⤇ β ⎬)) (Singleton _ p)) as R.
      destruct β.
      rewrite key_set_singleton.
      reflexivity.
      auto.
      unfold Δ'.
      split.
      rewrite Join_assoc_1 ; auto.
      eapply wf_union ; eauto.
      eapply r_wf_joinable ; auto. apply β_to_α. auto.
      repeat rewrite Join_key_set.
      eapply env_ptr_cons_included.
      rewrite Union_assoc.
      transitivity (key_set Γ'').
      auto.
      eapply Included_Union_1.
      rewrite <- Included_Singleton.
      rewrite Union_comm.
      transitivity (key_set (⎨ p ⤇ β ⎬)).
      rewrite R.
      reflexivity.
      eapply Included_Union_1.
      auto. auto.
      auto.
      assert (Δ' ⋈ Δ) as E1.
      unfold Δ'.
      eapply Joinable_join_intro_l ; eauto.
      rewrite joinable_comm.
      eapply Joinable_join_elim_2.
      eapply Hjble0.
      auto.
      auto.
      assert (Δ' ≃ add p β (Γ'' ∪ Γ)) as E'.
      unfold Δ'.
      eapply Join_add. auto.
      change ((Δ', (c, p :: η)) ∈ R( b, m', (AppTy_ρ f) d)) with
          (SetIn (R( b, m', (AppTy_ρ f) d)) (Δ', (c, p :: η))).
      heap_rewrite_realizer E'.
      eapply realizers_Equal'. rewrite -> H.
      simpl. fold t_ty_denot. unfold id.
      setoid_rewrite -> Smash_ValVal.
      rewrite -> kleisliVal. simpl. auto.
      apply Hgrab.
      apply test_gen_StepI with (i:=n). auto. auto.
  Qed.

  Lemma realizer_push:
    exists_fresh_pointer ->
    forall (m : nat) Γ i η ctx a b (ρ : ctx_denot ctx) n (f : ty_denot (a ⇾ b)),
      heap_wf Γ ->
      forall Q : nth_error ctx n = Some a,
        (Γ, η) ⊴ m | ρ ->
        (Γ, (i, η)) ∈ R(a ⇾ b, m, f) ->
        (Γ, (ipush n i, η)) ∈ R(b, m, AppTy_ρ f (lookup_nat _ _ Q ρ)) .
  Proof.
    intros EFP m Γ i η ctx a b ρ n f Γwf Q ρ_approx IH.
    eapply btop_weakened.
    - Case "Down Closed".
      intros fs m' m'' H m'_le_m''. eapply bbot_down_closed. apply m'_le_m''.
      apply H.
    - Case "Proof".
      intros (m', (Δ, s)) t_in m'_leq_m.
      set (d := lookup_nat _ _ Q ρ).
      destruct EFP with (Γ:=Γ ∪ Δ) (η:=η) (s:=s) as [p p_fresh].
      destruct m'. apply isatif_eq_Fullset.
      intros rwf twf Γ_Δ.
      set (H := env_realizer_lookup n _ _ _ _ _ Q ρ_approx).
      clearbody H.
      destruct H  as [q [EQ EX]].
      destruct EX as [α [β [F1 [? Hr2]]]].
      eapply antiex. constructor. apply EQ.
      assert (Γ ∪ Δ ≃ Γ ∪ (Γ ∪ Δ)) as E.
      rewrite <- Join_assoc_1.
      symmetry.
      eapply Equal_join_mor.
      rewrite Join_idem ; auto.
      apply Join_idem ; auto.
      reflexivity.
      eapply Joinable_refl ; auto.
      auto. auto.
      heap_rewrite_conf E.
      apply realizer_in_Ω with (a:=a ⇾ b) (d:=f).
      split.
      auto.
      eapply rwf.
      split.
      eapply wf_union ; eauto.
      rewrite Join_key_set.
      eapply stack_ptr_cons_included.
      transitivity (key_set Δ).
      eapply twf.
      auto with sets.
      rewrite <- Included_Singleton.
      transitivity (key_set Γ).
      rewrite Included_Singleton.
      eapply key_set_find_in.
      eauto.
      auto with sets.
      auto.
      eapply Joinable_join_intro_r.
      eapply Joinable_refl.
      auto. apply realizer_gen_StepI with (i:=m).
      apply le_Sn_le. auto. apply IH.
      assert (Γ ∪ Δ ≃ Γ ∪ Δ ∪ (⎨ q ⤇ β ⎬)) as E2.
      eapply find_singleton_Join.
      eapply find_submap.
      eapply join_sub1.
      auto. auto.
      heap_rewrite_test E2.
      apply tests_functional with (α:=α) (d:=lookup_nat n ctx Q ρ). apply H.
      eapply r_wf_find ; eauto.
      auto.
      auto.
      eapply Joinable_join_intro_l.
      eapply find_singleton_Joinable.
      auto.
      rewrite joinable_comm.
      eapply Joinable_submap.
      eauto.
      eapply Equal_submap_mor.
      reflexivity.
      eapply find_singleton_Join.
      eauto.
      eapply find_submap_singleton.
      eapply find_singleton_Joinable.
      auto. apply realizer_gen_StepI with (i:=m).
      apply le_Sn_le. auto. auto.
      apply test_StepI. auto.
  Qed.

  Lemma compiler_correctness_app :
    exists_fresh_pointer ->
    ∀ (c : ctx) (θ1 θ2 : type) (t0 : term c (θ1 ⇾ θ2)) (v : var c θ1) (i : Code)
      (d : ctx_denot c =-> ty_denot (θ1 ⇾ θ2)),
      (c ⊢ i ◀| d) →
      (c ⊢ (ipush (var_to_nat v) i) ◀| (AppTy d (lookup v))).
  Proof.
    intros EFP c θ1 θ2 t0 v i d IH.
    intros n Γ η ρ Γwf ρ_approx.
    eapply realizers_Equal'. by rewrite -> sem_term_app_Eq with (d:=d).
    set (Q := nth_var_to_nat v).
    clearbody Q.
    rewrite (var_to_nat_lookup v ρ Q).
    eapply realizer_push ; auto.
  Qed.

  Lemma tests_bop_1:
    ∀ (m : nat) (π : ctx) (bop : BOp) (Γ Γ': Heap) (i' : Code) (η η' : MEnv)
      (z : int_cpoType) (Δ : Heap) (s : stack) (p : Pointer)
      (d d' : ctx_denot π =-> ty_denot tint) (ρ : ctx_denot π),
      fresh_for_heap p (Γ ∪ Δ) ->
      d ρ =-= eta z ->
      (Γ, η) ⊴ m | ρ ->
      r_wf (Γ', (ival (iint z), η')) ->
      t_wf (Δ, s) ->
      Γ ⋈ Δ ->
      Γ' ⋈ Map.add p (K (ZBOpL i'), η) (Γ ∪ Δ) -> (* Γ' ⋈ Δ *)
      (m, (Δ, s))
        ∈
        @LiftRel tint ((((IntOpTy (semZBOp bop)) d) d') ρ) (Primitives tint) ⊥ ->
      SetIn (Tests tint (d' ρ))
            (m, (Map.add p (K (ZBOpR (iint z)), η') (Γ' ∪ Δ),
                 bopapply p bop :: s)).
  Proof.
    intros m π bop Γ Γ' i' η η' z Δ s p d d' ρ
           p_fresh dρ_eq_z ρ_approx_m Γ'wf Δwf Γ_Δ Γ'_ΓΔp t_Δ.
    eapply bbot_weakened.
    - Case "Down Closed".
      intros (Γ'',α') m' m'' H m'_le_m''. destruct H as [f' [? ?]].
      exists f'. split. auto.
      apply primitive_gen_StepI with (i:=m'). auto. auto.
    - Case "Proof".
      intros (m', (Γ'', (im, η''))) pr_m' m'_leq_m.
      destruct m'. apply isatif_eq_Fullset.
      rename m'_leq_m into Sm'_leq_m.
      intros Γ''wf ΓΔpwf Γ''_Γ'Δp.
      destruct pr_m' as [dm [? ?]].
      destruct im ; try contradiction.
      destruct v ; try contradiction. rename z0 into z'.
      eapply antiex. apply tbop_apply_3.
      apply heap_find_join_prop'. auto. right.
      apply F.add_eq_o. auto.
      assert(Γ'_Δ : Γ' ⋈ Δ).
      --  apply Join_fresh_add_prop in Γ'_ΓΔp.
          apply joinable_comm.
          eapply Joinable_join_elim_2. apply Γ_Δ. auto. apply p_fresh.
      assert (as0 : Γ'' ∪ Map.add p (K (ZBOpR (iint z)), η') (Γ' ∪ Δ)
                          ≃
                  (Γ'' ∪ Map.add p (K (ZBOpR (iint z)), η') Γ') ∪ Δ
           ).
    - (* begin as0 *)
      apply fresh_for_heap_join in p_fresh.
      rewrite -> Equal_join_mor. 2 : { auto. } 2 : { reflexivity. }
      2 : { rewrite <- heap_add_join_prop'.
            rewrite Join_comm_1.
            rewrite heap_add_join_prop.
            rewrite Join_comm_1.
            reflexivity.
            apply joinable_comm.
            apply Join_add_prop'. apply p_fresh. auto.
            apply p_fresh. auto.
            apply Join_add_prop''. auto. auto.
      } 2 : { auto. }
      rewrite <- Join_comm_1 in Γ''_Γ'Δp. 2 : { auto. }
      rewrite <- heap_add_join_prop' in Γ''_Γ'Δp. 2 : { auto. }
      rewrite <- Join_assoc_1. reflexivity.
      apply comp_join_elim_r with (Δ:=add p (K (ZBOpR (iint z)), η') Δ).
      apply Join_add_prop''. auto. auto.
      2 : { apply Join_add_prop. apply Joinable_fresh. apply p_fresh. auto. }
      apply comp_join_elim_l with (Σ:=add p (K (ZBOpR (iint z)), η') Γ').
      apply joinable_comm.
      apply Join_add_prop'. apply p_fresh. auto.
      rewrite <- heap_add_join_prop. auto. apply p_fresh. auto.
  (* end as0 *)
  heap_rewrite_conf as0.
  assert (as1 : (m',(Γ'' ∪ Map.add p (K (ZBOpR (iint z)), η') Γ',
                 (ival (iint (semZBOp bop z z')), η')))
                  ∈ @LiftRel tint ((((IntOpTy (semZBOp bop)) d) d') ρ)
                  (Primitives tint)).
  - (* begin as1 *)
    assert (as2 : (((IntOpTy (semZBOp bop)) d) d') ρ =-= eta (semZBOp bop z z')).
    -- (* begin as2 *)
      simpl. unfold id. destruct H0. rewrite -> H, -> dρ_eq_z, -> H1.
      setoid_rewrite -> Smash_ValVal.
      rewrite -> kleisliVal. by simpl.
    (* end as2 *)
    exists (semZBOp bop z z'). split. auto.
    split. rewrite Join_key_set.
    intros q q_in. apply Union_intror.
    apply F.add_in_iff. right. apply Γ'wf. auto.
    rewrite <- Join_comm_1 in Γ''_Γ'Δp. 2 : { auto. }
    rewrite <- heap_add_join_prop' in Γ''_Γ'Δp. 2 : { auto. }
    apply comp_join_elim_r with (Δ:=add p (K (ZBOpR (iint z)), η') Δ).
    apply Join_add_prop''. auto. auto. auto.
  (* end as1 *)
  apply test_gen_StepI with (j:=m') in t_Δ.
  specialize (t_Δ _ as1).  
  unfold "⊧", satif, mrel, isatif in t_Δ.
  rewrite -> Nat.min_id in t_Δ.
  apply t_Δ.
  unfold r_wf. split.
  apply wf_union.
  rewrite <- Join_comm_1 in Γ''_Γ'Δp. 2 : { auto. }
  rewrite <- heap_add_join_prop' in Γ''_Γ'Δp. 2 : { auto. }
  apply comp_join_elim_r with (Δ:=add p (K (ZBOpR (iint z)), η') Δ).
  apply Join_add_prop''. auto. auto.
  apply Γ''wf.
  apply wf_add. apply Γ'wf. apply Γ'wf.
  intros q q_in.
  apply join_in2.
  apply F.add_in_iff. right.
  apply Γ'wf. auto.
  auto.
  apply (fresh_for_heap_join Γ_Δ) in p_fresh.
  apply Joinable_join_intro_l.
  rewrite <- Join_comm_1 in Γ''_Γ'Δp. 2 : { auto. }
  rewrite <- heap_add_join_prop' in Γ''_Γ'Δp. 2 : { auto. }
  apply comp_join_elim_l with (Σ:=add p (K (ZBOpR (iint z)), η') Γ').
  apply joinable_comm.
  apply Join_add_prop'. apply p_fresh.
  auto. rewrite <- heap_add_join_prop. auto. apply p_fresh. auto.
  apply Join_add_prop'. apply p_fresh. auto.
  apply Nat.le_trans with (m:=m'.+1). auto. auto.
  Qed.
    
  Lemma tests_bop_2:
    ∀ (m : nat) (bop : BOp) (c : ctx) (Γ : Heap) (i i' : Code) (η : MEnv)
      (Δ : Heap) (s : stack) (p : Pointer)
      (d d' : ctx_denot c =-> ty_denot tint) (ρ : ctx_denot c),
      fresh_for_heap p (Γ ∪ Δ) ->
      (Γ, η) ⊴ m | ρ ->
      (c ⊢ i' ◀| d') ->
      ((m.+1, (Δ, s))
         ∈ @LiftRel tint ((((IntOpTy (semZBOp bop)) d) d') ρ)
         (Primitives tint) ⊥) ->
      r_wf (Γ, (ibop bop i i', η)) ->
      t_wf (Δ, s) ->
      Γ ⋈ Δ ->
      SetIn (Tests tint (d ρ))
            (m, (Map.add p (K (ZBOpL i'), η) (Γ ∪ Δ), bopapply p bop :: s)).
  Proof.
    intros m bop c Γ i i' η Δ s p d d' ρ p_fresh ρ_approx_m IH' t_Δ Γwf Δwf Γ_Δ.
    eapply bbot_weakened.
    - Case "Down Closed".
      intros (Γ',α') m' m'' H m'_le_m''. destruct H as [f' [? ?]].
      exists f'. split. auto.
      apply primitive_gen_StepI with (i:=m'). auto. auto.
    - Case "Proof".
      intros (m', (Γ', (im, η'))) r_m' m'_leq_m.
      destruct m'. apply isatif_eq_Fullset.
      rename m'_leq_m into Sm'_leq_m.
      intros Γ'wf ΓΔpwf Γ'_ΓΔp.
      destruct r_m' as [dm [? ?]].
      destruct im ; try contradiction.
      destruct v ; try contradiction.
      eapply antiex. constructor.
      apply heap_find_join_prop'. auto. right.
      apply F.add_eq_o. auto.
      assert (as0 : Map.add p (K (ZBOpR (iint z)), η')
                            (Γ' ∪ Map.add p (K (ZBOpL i'), η) (Γ ∪ Δ))
                            ≃
                            Γ ∪ (Map.add p (K (ZBOpR (iint z)), η') (Γ' ∪ Δ))
             ).
      -- SCase "as0".
         assert(Γ'_Γ : Γ' ⋈ Γ).
         ---  apply Join_fresh_add_prop in Γ'_ΓΔp.
              apply joinable_comm.
              eapply Joinable_join_elim_2.
              apply joinable_comm. apply Γ_Δ.
              rewrite Join_comm_1. auto. auto. apply p_fresh.
         assert(Γ'_Δ : Γ' ⋈ Δ).
         ---  apply Join_fresh_add_prop in Γ'_ΓΔp.
              apply joinable_comm.
              eapply Joinable_join_elim_2. apply Γ_Δ. auto. apply p_fresh.
              rewrite <- heap_add_join_prop'. 2 : { auto. }
              rewrite -> Equal_join_mor.
              2 : { apply Join_add_prop''. auto. }
              2 : { reflexivity. }
              2 : { rewrite heap_add_update_prop. reflexivity. }
              rewrite -> Equal_join_mor.
              2 : { apply Join_add_prop''.
                    apply Join_fresh_add_prop in Γ'_ΓΔp.
                    auto. apply p_fresh.
              }
              2 : { reflexivity. }
              2 : { rewrite <- heap_add_join_prop'. reflexivity. auto. }
              rewrite <- Join_assoc_1.
              rewrite -> Equal_join_mor.
              2 : { rewrite Join_comm_1.
                    rewrite -> heap_add_join_prop'.
                    apply Join_add_prop''. apply Joinable_join_intro_l; auto.
                    auto.
                    apply Join_add_prop''. auto.
              }
              2 : { rewrite Join_comm_1. reflexivity.
                    apply Join_add_prop''. auto.
              }
              2 : { reflexivity. }
              2 : { apply Join_add_prop''. auto. }
              2 : { apply Join_add_prop''. auto. }
              2 : { apply Join_add_prop''. auto. }
              rewrite -> Join_assoc_1.
              rewrite -> Equal_join_mor.
              2 : { apply Joinable_join_intro_r.
                    apply Join_add_prop''. auto.
                    apply Join_add_prop''. auto.
              }
              2 : { reflexivity. }
              2 : { rewrite -> heap_add_join_prop'. reflexivity. auto. }
              2 : { apply Join_add_prop''. auto. }
              2 : { apply Join_add_prop''. auto. }
              2 : { apply Join_add_prop''. auto. }
              rewrite -> heap_add_join_prop. reflexivity.
              apply fresh_for_heap_join in p_fresh. apply p_fresh. auto. auto.
      (* end as0 *)
      heap_rewrite_conf as0.
      have m'_leq_m := Nat.le_trans m' (m'.+1) m
                                   (Nat.lt_le_incl m' (m'.+1)
                                                   (Nat.lt_succ_diag_r m'))
                                   Sm'_leq_m.
      have ρ_approx_m' := env_realizer_gen_StepI _ _ _ _ m'_leq_m ρ_approx_m.
      assert (as1 : SetIn (Tests tint (d' ρ))
                          (m', (Map.add p (K (ZBOpR (iint z)), η') (Γ' ∪ Δ),
                                bopapply p bop :: s))).
      eapply tests_bop_1 with (d:=d). apply p_fresh. destruct H0.
      rewrite <- H1. auto. apply ρ_approx_m'. auto. auto. auto.
      apply Γ'_ΓΔp. apply test_gen_StepI with (i:=m.+1).
      apply Nat.le_trans with (m:=m).
      apply Nat.le_trans with (m:=m'.+1). auto. auto. auto.
      auto.
      specialize (IH' m' Γ η ρ (fst Γwf) ρ_approx_m' _ as1).
      unfold "⊧", satif, mrel, isatif in IH'.
      rewrite -> Nat.min_id in IH'.
      apply IH'. auto.
      split. split.
      intros q q_in. destruct q_in. auto.
      destruct H1 as [k [? [? [? ?]]]].
      apply F.add_mapsto_iff in H1. destruct H1. destruct H1.
      apply F.add_in_iff. inversion H3. right.
      apply join_in1. apply Γ'wf. rewrite <- H6 in *. apply H2.
      destruct H1.
      apply F.add_in_iff. right.
      apply join_MapsTo in H3. destruct H3.
      apply join_in1. destruct Γ'wf. apply H4.
      apply Union_intror. exists k, x0, x1. auto.
      apply join_in2. destruct Δwf. apply H4.
      apply Union_intror.  exists k, x0, x1. auto.
      intros q q_in. apply Union_introl. auto.
      intros q q_in.
      destruct q_in. inversion H1. inversion H2.
      apply F.add_in_iff. right.
      apply join_in2. apply Δwf. left. apply H2.
      inversion H1. inversion H2. inversion H3.
      apply F.add_in_iff. right.
      apply join_in2. apply Δwf. right. left. apply H3.
      inversion H2. inversion H3. inversion H4.
      apply F.add_in_iff. right.
      apply join_in2. apply Δwf. right. right. left. apply H4.
      inversion H3. inversion H4. inversion H5.
      apply F.add_in_iff. right.
      apply join_in2. apply Δwf. right. right. right. left. apply H5.
      inversion H4. inversion H5. inversion H6. inversion H7.
      apply F.add_in_iff. left. auto.
      apply F.add_in_iff. right.
      apply join_in2. apply Δwf. right. right. right. right. left. exists x. auto.
      inversion H5. inversion H6.
      apply F.add_in_iff. right.
      apply join_in2. apply Δwf. right. right. right. right. right. auto.
      apply joinable_comm.
      apply Join_add_prop'.
      apply (fresh_for_heap_join Γ_Δ p_fresh).
      assert(Γ'_Γ : Γ' ⋈ Γ).
      --  apply Join_fresh_add_prop in Γ'_ΓΔp.
          apply joinable_comm.
          eapply Joinable_join_elim_2.
          apply joinable_comm. apply Γ_Δ.
          rewrite Join_comm_1. auto. auto. apply p_fresh.
          apply Joinable_join_intro_l. auto. auto.
  Qed.

  Lemma compiler_correctness_bop:
    ∀ (bop : BOp) (π : ctx) (i i' : Code)
      (d d' : ctx_denot π =-> ty_denot tint),
      exists_fresh_pointer ->
      (π ⊢ i ◀| d) ->
      (π ⊢ i' ◀| d') ->
      (@GRealizers π tint (IntOpTy (semZBOp bop) d d') (ibop bop i i')).
  Proof.
    intros bop c i i' d d' EFP IH IH'.
    intros n Γ η ρ Γwf ρ_approx.
    eapply btop_weakened.
    - Case "Down Closed".
      intros fs m m' H m_le_m'. eapply bbot_down_closed. apply m_le_m'. apply H.
    - Case "Proof".
      intros (m, (Δ, s)) t_in m_leq_n.
      destruct EFP with (Γ:=Γ ∪ Δ) (η:=η) (s:=s) as [p p_fresh].
      destruct m. apply isatif_eq_Fullset.
      rename m_leq_n into Sm_leq_n.
      intros Γwf' Δwf Γ_Δ.
      eapply antiex. constructor. apply p_fresh.
      have m_leq_n := Nat.le_trans m (m.+1) n
                                  (Nat.lt_le_incl m (m.+1)
                                                  (Nat.lt_succ_diag_r m))
                                  Sm_leq_n.
      have ρ_approx_m := env_realizer_gen_StepI _ _ _ _ m_leq_n ρ_approx.
      assert (as0 : SetIn (Tests tint (d ρ))
                (m, (Map.add p (K (ZBOpL i'), η) (Γ ∪ Δ), bopapply p bop :: s))).
      eapply tests_bop_2. destruct p_fresh. auto. auto. apply IH'. auto.
      apply Γwf'. auto. auto.
      specialize (IH m Γ η  ρ Γwf ρ_approx_m _ as0).
      assert (as1 : Γ ∪ Map.add p (K (ZBOpL i'), η) (Γ ∪ Δ) ≃
                      Map.add p (K (ZBOpL i'), η) (Γ ∪ Δ)).
      - (* as1 *)
        destruct p_fresh.
        assert (H' := H).
        apply fresh_for_heap_join in H.
        rewrite Join_comm_1.
        rewrite <- heap_add_prop_idemp'''.
        reflexivity. apply H.
        auto. auto. rewrite <- Join_add.
        apply Joinable_join_intro_r.
        apply Joinable_join_intro_r.
        apply Joinable_refl. auto.
        apply Joinable_fresh. apply H.
        apply Joinable_fresh. apply H'.
        auto.
      symmetry in as1.
      heap_rewrite_conf as1.
      unfold "⊧", satif, mrel, isatif in IH.
      rewrite -> Nat.min_id in IH.
      apply IH. auto.
      split. split.
      intros q q_in. destruct q_in. auto.
      destruct H as [k [? [? [? ?]]]].
      apply F.add_mapsto_iff in H. destruct H. destruct H.
      apply F.add_in_iff. inversion H1. right.
      apply join_in1. apply Γwf'. rewrite <- H4 in *. apply H0.
      destruct H.
      apply F.add_in_iff. right.
      apply join_MapsTo in H1. destruct H1.
      apply join_in1. destruct Γwf'. apply H2.
      apply Union_intror. exists k, x0, x1. auto.
      apply join_in2. destruct Δwf. apply H2.
      apply Union_intror.  exists k, x0, x1. auto.
      intros q q_in. apply Union_introl. auto.
      intros q q_in.
      destruct q_in. inversion H. inversion H0.
      apply F.add_in_iff. right.
      apply join_in2. apply Δwf. left. apply H0.
      inversion H. inversion H0. inversion H1.
      apply F.add_in_iff. right.
      apply join_in2. apply Δwf. right. left. apply H1.
      inversion H0. inversion H1. inversion H2.
      apply F.add_in_iff. right.
      apply join_in2. apply Δwf. right. right. left. apply H2.
      inversion H1. inversion H2. inversion H3.
      apply F.add_in_iff. right.
      apply join_in2. apply Δwf. right. right. right. left. apply H3.
      inversion H2. inversion H3. inversion H4. inversion H5.
      apply F.add_in_iff. left. auto.
      apply F.add_in_iff. right.
      apply join_in2. apply Δwf. right. right. right. right. left. exists x. auto.
      inversion H3. inversion H4.
      apply F.add_in_iff. right.
      apply join_in2. apply Δwf. right. right. right. right. right. auto.
      apply joinable_comm.
      apply Join_add_prop'. destruct p_fresh.
      apply (fresh_for_heap_join Γ_Δ H).
      apply Joinable_join_intro_l. apply Joinable_refl.
      auto.
  Qed.
  
  Lemma ifz_conf_prop : forall n Γ Γ' Δ α i i' p η s,
      fresh_for_heap p (Γ ∪ Δ) ->
      r_wf (Γ, (i, η)) ->
      t_wf (Δ, s) ->
      Γ ⋈ Δ ->
      Γ' ⋈ Map.add p (α, η) (Γ ∪ Δ) ->
      SetIn (Ω n) (Γ ∪ Δ, (i', η), s) ->
      SetIn (Ω n) (Γ' ∪ Map.add p (α, η) (Γ ∪ Δ), (i', η), s).
  Proof.
    intros n Γ Γ' Δ α i i' p η s p_fresh Γwf Δwf Γ_Δ Γ'_pΓΔ w_in.
    have hp := heaps_prop_ifz p_fresh Γ_Δ Γ'_pΓΔ.
    heap_rewrite_conf hp. clear hp.
    apply extend_heap.
    apply Joinable_join_intro_r.
    apply joinable_comm.
    eapply Join_fresh_add_prop. apply p_fresh. apply Γ'_pΓΔ.
    apply Joinable_join_intro_l.
    apply joinable_comm.
    apply Join_add_prop'. apply fresh_for_heap_join in p_fresh. apply p_fresh.
    auto. auto.
    apply joinable_comm. apply Join_add_prop'.
    apply fresh_for_heap_join in p_fresh. apply p_fresh. auto.
    apply Joinable_refl.
    split. apply wf_union. auto. apply Γwf. apply Δwf.
    split. intros q q_in. apply join_in1. apply Γwf. auto.
    intros q q_in. apply join_in2. apply Δwf. auto.
    auto.
  Qed.

  Lemma tests_ifz:
  ∀ (n : nat) (c : ctx) (θ : type) (ig i i' : Code) (dg : cpoCatType 
                                               (ctx_denot c) 
                                               (ty_denot tint)) 
    (d d' : cpoCatType (ctx_denot c) (ty_denot θ))
    (Γ : Heap) (η : MEnv) (ρ : ctx_denot c)
    (Δ : Heap) (s : stack) (p : Pointer),
    fresh_for_heap p (Γ ∪ Δ) ->
    r_wf (Γ, (iifz ig i i', η)) ->
    t_wf (Δ, s) ->
    Γ ⋈ Δ ->
    ((Γ, η) ⊴ n | ρ) ->
    (c ⊢ i ◀| d) ->
    (c ⊢ i' ◀| d') ->
    (n, (Δ, s)) ∈ LiftRel ((((IfZIntTy dg) d) d') ρ) (Primitives θ) ⊥ ->
    SetIn  (Tests tint (dg ρ))
                            (n, (Map.add p  (K (IfZ i i'), η)(Γ ∪ Δ), ? p :: s)).
  Proof.
    intros n c θ ig i i' dg d d' Γ η ρ Δ s p p_fresh Γwf Δwf Γ_Δ
           ρ_approx_n IH IH' t_in.
    eapply bbot_weakened.
    - Case "Down Closed".
      intros (Γ',α') m' m'' H m'_le_m''. destruct H as [f' [? ?]].
      exists f'. split. auto.
      apply primitive_gen_StepI with (i:=m'). auto. auto.
    - Case "Proof".
      intros (m, (Γ', (im, η'))) r_m m_leq_n.
      destruct m. apply isatif_eq_Fullset.
      rename m_leq_n into Sm_leq_n.
      intros Γ'wf ΓΔpwf Γ'_ΓΔp.
      destruct r_m as [dm [? ?]].
      destruct im ; try contradiction.
      destruct v ; try contradiction. destruct H0. rewrite -> H1 in H. clear H1.
      have m_leq_n := Nat.le_trans m (m.+1) n
                                  (Nat.lt_le_incl m (m.+1)
                                                  (Nat.lt_succ_diag_r m))
                                  Sm_leq_n.
      have ρ_approx_m := env_realizer_gen_StepI _ _ _ _ m_leq_n ρ_approx_n.
      destruct z.
      -- SCase "z = 0".
         eapply antiex. eapply tifz_0.
         apply heap_find_join_prop'. auto. right.
         apply F.add_eq_o. auto.
         eapply ifz_conf_prop. apply p_fresh. apply Γwf. auto. auto. auto.
         destruct Γwf.
         eapply Tests_Equal' in t_in. 2 : {
           simpl. setoid_rewrite -> H. simpl. unfold id.
           setoid_rewrite -> Smash_ValVal.
           rewrite -> kleisliVal. simpl. setoid_rewrite -> Smash_ValVal.
           rewrite -> kleisliVal. by simpl. }
         apply test_gen_StepI with (j:=m) in t_in. 2 : { auto. }
         specialize (IH m Γ η ρ H1 ρ_approx_m _ t_in).
         unfold "⊧", satif, mrel, isatif in IH.
         rewrite -> Nat.min_id in IH. apply IH. split. auto. auto. auto. auto.
      -- SCase "z > 0".
         eapply antiex. eapply tifz_n0.
         apply heap_find_join_prop'. auto. right.
         apply F.add_eq_o. auto. intro pos_eq_Z0. inversion pos_eq_Z0.
         eapply ifz_conf_prop. apply p_fresh. apply Γwf. auto. auto. auto.
         destruct Γwf.
         eapply Tests_Equal' in t_in. 2 : {
           simpl. setoid_rewrite -> H. simpl. unfold id.
           setoid_rewrite -> Smash_ValVal.
           rewrite -> kleisliVal. simpl. setoid_rewrite -> Smash_ValVal.
           rewrite -> kleisliVal. by simpl. }
         apply test_gen_StepI with (j:=m) in t_in. 2 : { auto. }
         specialize (IH' m Γ η ρ H1 ρ_approx_m _ t_in).
         unfold "⊧", satif, mrel, isatif in IH'.
         rewrite -> Nat.min_id in IH'. apply IH'. split. auto. auto. auto. auto.
      -- SCase "z < 0".
         eapply antiex. eapply tifz_n0.
         apply heap_find_join_prop'. auto. right.
         apply F.add_eq_o. auto. intro pos_eq_Z0. inversion pos_eq_Z0.
         eapply ifz_conf_prop. apply p_fresh. apply Γwf. auto. auto. auto.
         destruct Γwf.
         eapply Tests_Equal' in t_in. 2 : {
           simpl. setoid_rewrite -> H. simpl. unfold id.
           setoid_rewrite -> Smash_ValVal.
           rewrite -> kleisliVal. simpl. setoid_rewrite -> Smash_ValVal.
           rewrite -> kleisliVal. by simpl. }
         apply test_gen_StepI with (j:=m) in t_in. 2 : { auto. }
         specialize (IH' m Γ η ρ H1 ρ_approx_m _ t_in).
         unfold "⊧", satif, mrel, isatif in IH'.
         rewrite -> Nat.min_id in IH'. apply IH'. split. auto. auto. auto. auto.
  Qed.
  
  Lemma compiler_correctness_ifz:
    exists_fresh_pointer →
    ∀ (π : ctx) (θ : type) (ig i i' : Code)
      (dg : ctx_denot π =-> ty_denot tint)
      (d d' : ctx_denot π =-> ty_denot θ),
      (π ⊢ ig ◀| dg) →
      (π ⊢ i ◀| d) →
      (π ⊢ i' ◀| d') →
      (π ⊢ (iifz ig i i') ◀| IfZIntTy dg d d').
  Proof.
    intros EFP c θ ig i i' dg d d' IHg IH IH'.
    intros n Γ η ρ Γwf ρ_approx_n.
    eapply btop_weakened.
    - Case "Down Closed".
      intros fs m m' H m_le_m'. eapply bbot_down_closed. apply m_le_m'. apply H.
    - Case "Proof".
      intros (m, (Δ, s)) t_in m_leq_n.
      destruct EFP with (Γ:=Γ ∪ Δ) (η:=η) (s:=s) as [p p_fresh].
      destruct m. apply isatif_eq_Fullset.
      rename m_leq_n into Sm_leq_n.
      intros Γwf' Δwf Γ_Δ.
      eapply antiex. constructor. apply p_fresh.
      assert (p_fresh_ΓΔηs:=p_fresh).
      destruct p_fresh. apply (fresh_for_heap_join Γ_Δ) in H.
      assert (as0 : add p (K (IfZ i i'), η) (Γ ∪ Δ)
                          ≃
                  Γ ∪ add p (K (IfZ i i'), η) (Γ ∪ Δ)
           ).
      -- (* begin as0 *)
        symmetry.
        rewrite Join_comm_1. rewrite <- heap_add_prop_idemp'''. reflexivity.
        apply H. auto. apply joinable_comm. apply Join_add_prop'. apply H.
        apply joinable_comm. apply joinable_join1. auto.
      (* end as0 *)
      have m_leq_n := Nat.le_trans m (m.+1) n
                                   (Nat.lt_le_incl m (m.+1)
                                                   (Nat.lt_succ_diag_r m))
                                   Sm_leq_n.
      have ρ_approx_m := env_realizer_gen_StepI _ _ _ _ m_leq_n ρ_approx_n.
      -- assert (as1 : SetIn (Tests tint (dg ρ))
                             (m, (Map.add p (K (IfZ i i'), η) (Γ ∪ Δ), ? p :: s))
                ).
         apply tests_ifz with (ig:=ig) (θ:=θ) (d:=d) (d':=d').
         apply fresh_for_heap_join_1. auto. auto. auto. auto. auto. auto.
         auto. auto. apply test_StepI. auto.
      heap_rewrite_conf as0.
      specialize (IHg m Γ η ρ Γwf ρ_approx_m _ as1).
      unfold "⊧", satif, mrel, isatif in IHg.
      rewrite -> Nat.min_id in IHg.
      apply IHg. auto.
      split. apply wf_add. apply wf_union. auto. apply Γwf. apply Δwf.
      intros q q_in. apply join_in1. apply Γwf'. auto.
      apply stack_ptr_cons_included_if.
      intros q q_in. apply F.add_in_iff. right. apply join_in2. apply Δwf. auto.
      apply F.add_in_iff. left. auto.
      apply joinable_comm. apply Join_add_prop'. apply H.
      apply joinable_comm. apply joinable_join1. auto.
  Qed.

  Lemma compiler_correctness_pair:
    exists_fresh_pointer →
    ∀ (π : ctx) (θ1 θ2 : type) (i i' : Code)
      (d  : ctx_denot π =-> ty_denot θ1)
      (d' : ctx_denot π =-> ty_denot θ2),
      (π ⊢ i ◀| d) ->
      (π ⊢ i' ◀| d') ->
      (@GRealizers π (θ1 ⨱ θ2) (eta << <| d , d' |>) (ival (ipair i i'))).
  Proof.
    intros EFP c θ1 θ2 i i' d d' IH IH'.
    intros n Γ η ρ Γwf ρ_approx_n.
    eapply primitive_realizer.
    split.
    eapply env_realizer_ptr. auto. apply ρ_approx_n.
    intros m m_le_n.
    split.
    apply IH. auto. apply env_realizer_gen_StepI with (i:=n).
    apply Nat.lt_le_incl. auto. auto.
    apply IH'. auto. apply env_realizer_gen_StepI with (i:=n).
    apply Nat.lt_le_incl. auto. auto.
  Qed.

  Lemma tests_pairs_1 :
    forall n Γ Δ s θ1 θ2 (d1d2 : ty_denot (θ1 ⨱ θ2)),
    t_wf (Δ, s) ->
    Γ ⋈ Δ ->
    SetIn (Tests θ1 (kleisli (FST (ty_denot θ1) (ty_denot θ2)) d1d2))
          (n, (Δ, s)) ->
    SetIn (Tests (θ1 ⨱ θ2) d1d2) (n, (Γ ∪ Δ, mapplypi1 :: s)).
  Proof.
    intros n Γ Δ s θ1 θ2 d1d2 Δwf Γ_Δ t_in.
    eapply bbot_weakened.
    - Case "Down Closed".
      intros (Γ',α') m' m'' H m'_le_m''. destruct H as [f' [? ?]].
      exists f'. split. auto.
      apply primitive_gen_StepI with (i:=m'). auto. auto.
    - Case "Proof".
      intros (m, (Γ', (im, η'))) r_m m_leq_n.
      destruct m. apply isatif_eq_Fullset.
      rename m_leq_n into Sm_leq_n.
      intros Γ'wf ΓΔpwf Γ'_ΓΔp.
      destruct r_m as [dm [? ?]].
      destruct im ; try contradiction.
      destruct v ; try contradiction.
      eapply antiex. constructor. destruct dm as [d1 d2].
      eapply Tests_Equal' in t_in.
      2 : { rewrite -> H. simpl. rewrite -> kleisliVal. by simpl. }
      destruct H0. assert ((m < m.+1)%coq_nat) by auto.
      specialize (H1 _ H2) as [? ?]. clear H2. simpl in H1.
      apply test_gen_StepI with (j:=m) in t_in. 2 : {
      apply (Nat.le_trans m (m.+1) n (Nat.lt_le_incl m (m.+1)
                                                     (Nat.lt_succ_diag_r m))
                          Sm_leq_n). }
      specialize (H1 _ t_in). simpl in H1.
      simpl in *. destruct Γ'wf.
      apply joinable_comm in Γ'_ΓΔp.
      have ble := Joinable_join_elim_2 Γ_Δ Γ'_ΓΔp.
      have bla := Joinable_join_elim_1 Γ_Δ Γ'_ΓΔp.
      destruct Δwf.
      assert (Γ' ∪ (Γ ∪ Δ) ≃ (Γ' ∪ Δ) ∪ Γ) as E.
      -- (* Assert *)
        rewrite -> Join_assoc_1.
        apply Equal_join_mor. auto. reflexivity.
        auto. auto. auto. auto.
    heap_rewrite_conf E.
    apply extend_heap; auto.
    split.
    apply wf_union. auto. auto. auto.
    split.
    rewrite Join_key_set.
    intros a b. apply Union_introl. auto. auto.
    rewrite Join_key_set.
    intros a b. apply Union_intror. auto. auto.
    rewrite -> Nat.min_id in H1.
    apply H1. auto. auto. auto.
    Qed.
  
  Lemma tests_pairs_2 :
    forall n Γ Δ s θ1 θ2 (d1d2 : ty_denot (θ1 ⨱ θ2)),
    t_wf (Δ, s) ->
    Γ ⋈ Δ ->
    SetIn (Tests θ2 (kleisli (SND (ty_denot θ1) (ty_denot θ2)) d1d2))
          (n, (Δ, s)) ->
    SetIn (Tests (θ1 ⨱ θ2) d1d2) (n, (Γ ∪ Δ, mapplypi2 :: s)).
  Proof.
    intros n Γ Δ s θ1 θ2 d1d2 Δwf Γ_Δ t_in.
    eapply bbot_weakened.
    - Case "Down Closed".
      intros (Γ',α') m' m'' H m'_le_m''. destruct H as [f' [? ?]].
      exists f'. split. auto.
      apply primitive_gen_StepI with (i:=m'). auto. auto.
    - Case "Proof".
      intros (m, (Γ', (im, η'))) r_m m_leq_n.
      destruct m. apply isatif_eq_Fullset.
      rename m_leq_n into Sm_leq_n.
      intros Γ'wf ΓΔpwf Γ'_ΓΔp.
      destruct r_m as [dm [? ?]].
      destruct im ; try contradiction.
      destruct v ; try contradiction.
      eapply antiex. constructor. destruct dm as [d1 d2].
      eapply Tests_Equal' in t_in.
      2 : { rewrite -> H. simpl. rewrite -> kleisliVal. by simpl. }
      destruct H0. assert ((m < m.+1)%coq_nat) by auto.
      specialize (H1 _ H2) as [? ?]. clear H2. simpl in H3.
      apply test_gen_StepI with (j:=m) in t_in. 2 : {
      apply (Nat.le_trans m (m.+1) n (Nat.lt_le_incl m (m.+1)
                                                     (Nat.lt_succ_diag_r m))
                          Sm_leq_n). }
      specialize (H3 _ t_in). simpl in H3.
      simpl in *. destruct Γ'wf.
      apply joinable_comm in Γ'_ΓΔp.
      have ble := Joinable_join_elim_2 Γ_Δ Γ'_ΓΔp.
      have bla := Joinable_join_elim_1 Γ_Δ Γ'_ΓΔp.
      destruct Δwf.
      assert (Γ' ∪ (Γ ∪ Δ) ≃ (Γ' ∪ Δ) ∪ Γ) as E.
      -- (* Assert *)
        rewrite -> Join_assoc_1.
        apply Equal_join_mor. auto. reflexivity.
        auto. auto. auto. auto.
    heap_rewrite_conf E.
    apply extend_heap; auto.
    split.
    apply wf_union. auto. auto. auto.
    split.
    rewrite Join_key_set.
    intros a b. apply Union_introl. auto. auto.
    rewrite Join_key_set.
    intros a b. apply Union_intror. auto. auto.
    rewrite -> Nat.min_id in H3.
    apply H3. auto. auto. auto.
  Qed.

  Lemma compiler_correctness_fst:
    ∀ (θ1 θ2 : type) (c : ctx) (v : var c (θ1 ⨱ θ2)),
      @GRealizers c θ1
                  (kleisli (FST (ty_denot θ1) (ty_denot θ2)) << lookup v)
                  (ifst (var_to_nat v)).
  Proof.
    intros θ1 θ2 c v.
    intros n Γ η ρ Γwf ρ_approx_n.
    eapply btop_weakened.
    - Case "Down Closed".
      intros fs m m' H m_le_m'. eapply bbot_down_closed. apply m_le_m'. apply H.
    - Case "Proof".
      intros (m, (Δ, s)) t_in m_leq_n.
      destruct m. apply isatif_eq_Fullset.
      rename m_leq_n into Sm_leq_n.
      intros Γwf' Δwf Γ_Δ.
      set (Q := nth_var_to_nat v); clearbody Q.
      set (H := env_realizer_lookup _ _ _ _ _ _ Q ρ_approx_n).
      clearbody H.
      destruct H  as [p [EQ EX]].
      destruct EX as [α [β [F1 [β_to_α Hr2]]]].
      eapply antiex. econstructor. apply EQ.
      eapply find_submap. apply join_sub1. auto. apply F1. apply β_to_α.
      eapply add_marker_pi1.
      eapply find_submap. apply join_sub1. auto. apply F1. apply β_to_α.
      rewrite <- var_to_nat_lookup in Hr2.
      assert (p_in_Γ : p ∈ heap_ptr Γ).
      unfold "∈", heap_ptr.
      apply Union_introl. eapply key_set_find_in.
      apply F1.
      apply test_StepI in t_in.
      apply realizer_gen_StepI with (j:=m) in Hr2. 2 : {
      apply (Nat.le_trans m (m.+1) n (Nat.lt_le_incl m (m.+1)
                                                     (Nat.lt_succ_diag_r m))
                          Sm_leq_n). }
      have TestsPair1 := @tests_pairs_1 m Γ Δ s θ1 θ2 (lookup v ρ) Δwf Γ_Δ t_in.
      assert (Γ ∪ Δ ≃ Γ ∪ (Γ ∪ Δ)) as H.
      rewrite <- Join_assoc_1.
      symmetry.
      eapply Equal_join_mor.
      rewrite Join_idem ; auto.
      apply Join_idem ; auto.
      reflexivity.
      eapply Joinable_refl ; auto.
      auto. auto.
      apply tests_realizers in TestsPair1.
      specialize (TestsPair1 (m,(Γ,α))).
      heap_rewrite_conf H.
      unfold "⊧", satif, mrel, isatif in TestsPair1.
      rewrite -> Nat.min_id in TestsPair1.
      apply TestsPair1.
      apply Hr2. 
      eapply r_wf_find. auto. apply F1. apply β_to_α.
      split.
      apply wf_union. auto. auto.
      apply (t_wf_heap Δwf).
      rewrite stack_ptr_eq_1.
      destruct Δwf.
      rewrite (Join_key_set Γ_Δ).
      right. apply H1. auto.
      apply joinable_join1. auto.
  Qed.

  Lemma compiler_correctness_snd:
    ∀ (θ1 θ2 : type) (c : ctx) (v : var c (θ1 ⨱ θ2)),
      @GRealizers c θ2
                  (kleisli (SND (ty_denot θ1) (ty_denot θ2)) << lookup v)
                  (isnd (var_to_nat v)).
  Proof.
    intros θ1 θ2 c v.
    intros n Γ η ρ Γwf ρ_approx_n.
    eapply btop_weakened.
    - Case "Down Closed".
      intros fs m m' H m_le_m'. eapply bbot_down_closed. apply m_le_m'. apply H.
    - Case "Proof".
      intros (m, (Δ, s)) t_in m_leq_n.
      destruct m. apply isatif_eq_Fullset.
      rename m_leq_n into Sm_leq_n.
      intros Γwf' Δwf Γ_Δ.
      set (Q := nth_var_to_nat v); clearbody Q.
      set (H := env_realizer_lookup _ _ _ _ _ _ Q ρ_approx_n).
      clearbody H.
      destruct H  as [p [EQ EX]].
      destruct EX as [α [β [F1 [β_to_α Hr2]]]].
      eapply antiex. econstructor. apply EQ.
      eapply find_submap. apply join_sub1. auto. apply F1. apply β_to_α.
      eapply add_marker_pi2.
      eapply find_submap. apply join_sub1. auto. apply F1. apply β_to_α.
      rewrite <- var_to_nat_lookup in Hr2.
      assert (p_in_Γ : p ∈ heap_ptr Γ).
      unfold "∈", heap_ptr.
      apply Union_introl. eapply key_set_find_in.
      apply F1.
      apply test_StepI in t_in.
      apply realizer_gen_StepI with (j:=m) in Hr2. 2 : {
      apply (Nat.le_trans m (m.+1) n (Nat.lt_le_incl m (m.+1)
                                                     (Nat.lt_succ_diag_r m))
                          Sm_leq_n). }
      have TestsPair2 := @tests_pairs_2 m Γ Δ s θ1 θ2 (lookup v ρ) Δwf Γ_Δ t_in.
      assert (Γ ∪ Δ ≃ Γ ∪ (Γ ∪ Δ)) as H.
      rewrite <- Join_assoc_1.
      symmetry.
      eapply Equal_join_mor.
      rewrite Join_idem ; auto.
      apply Join_idem ; auto.
      reflexivity.
      eapply Joinable_refl ; auto.
      auto. auto.
      apply tests_realizers in TestsPair2.
      specialize (TestsPair2 (m,(Γ,α))).
      heap_rewrite_conf H.
      unfold "⊧", satif, mrel, isatif in TestsPair2.
      rewrite -> Nat.min_id in TestsPair2.
      apply TestsPair2.
      apply Hr2. 
      eapply r_wf_find. auto. apply F1. apply β_to_α.
      split.
      apply wf_union. auto. auto.
      apply (t_wf_heap Δwf).
      rewrite stack_ptr_eq_2.
      destruct Δwf.
      rewrite (Join_key_set Γ_Δ).
      right. apply H1. auto.
      apply joinable_join1. auto.
  Qed.

  Theorem compiler_correctness :
    exists_fresh_pointer ->
    forall (π : ctx) (θ : type) (t : term π θ), (π ⊢ (⦇ t ⦈) ◀| (⟦ t ⟧)).
  Proof.
    intro EFP. induction t0.
    - Case "term_unit".
      apply compiler_correctness_unit.
    - Case "term_int".
      apply compiler_correctness_int.
    - Case "term_var".
      apply compiler_correctness_var.
    - Case "term_abs".
      apply compiler_correctness_abs; auto.
    - Case "term_app".
      apply compiler_correctness_app; auto.
    - Case "term_let".
      apply compiler_correctness_let; auto.
    - Case "term_bop".
      apply compiler_correctness_bop; auto.
    - Case "term_ifz".
      apply compiler_correctness_ifz; auto.
    - Case "term_pair".
      apply compiler_correctness_pair; auto.
    - Case "term_fst".
      apply compiler_correctness_fst.
    - Case "term_snd".
      apply compiler_correctness_snd.
  Qed.

End OperApprox.
