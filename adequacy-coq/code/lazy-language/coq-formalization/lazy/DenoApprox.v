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
Require Import Obs.
Require Import Syntax.
Require Import Semantics.
Require Import Compiler.
Require Import Coq.Program.Equality.
Require Import Sets.
Require Import Equalities.
Require Import ZArith.
Require Import BOp.

Require Import domoprs.
Require Import DomainStuff.
Require Import PredomAll.
Require Import uniirec.

Include RD.

From mathcomp Require Import ssreflect.

(** * Realizers, Tests and Main Theorem *)

Module DenoApprox (PointerType : UsualDecidableType)
                  (Import Ob : Observations PointerType).

  Definition RType : Type := Heap * MClos.
  Definition TType : Type := Heap * stack.
  Definition EType : Type := Heap * MEnv.

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

  (** Concrete definition of the satisfability relation *)
  Definition satif (r : RType) (t : TType) : Prop :=
    match r, t with
      (Γ, α), (Δ, s) =>
      r_wf (Γ, α) -> t_wf (Δ, s) ->  Γ ⋈ Δ -> SetIn Ω (Γ ∪ Δ, α, s)
    end.

  Module TestRealizer <: TstElt.
    Definition Elt := RType.
    Definition Tst := TType.
    Definition satif := satif.
  End TestRealizer.
  
  Module Import OO := Biorthogonality TestRealizer.

  Notation flipIn A x S := (Ensembles.In A S x).

  Reserved Notation "t_Rp( θ , d )" (at level 70, no associativity).
  Infix "∈" := (flipIn _) (at level 80, no associativity).
  Infix "⊆" := (Ensembles.Included _) (at level 80, no associativity).

  (** Primitive realizers *)
  Fixpoint Primitives (θ : type) : t_ty_denot θ -> Ensemble RType :=
    let R θ d :=
        fun r => forall (d' : t_ty_denot θ), d =-= eta d' -> r ∈ (Primitives θ d') ⊥ ⊤ in
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
            forall d Γ' α β,
              (Γ', α) ∈ R θ1 d  ->
              r_wf (Γ', α) ->
              Γ ⋈ Γ'  ->
              MClos_to_HClos α = β ->
              forall p, (Γ ∪ Γ') ⋈ ⎨ p ⤇ β ⎬ ->
                   (add p β (Γ ∪ Γ'), (i, p :: η)) ∈ R θ2 (f d)
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
      let condition Γ i i' η :=
          (Γ, (i, η)) ∈ R θ1 (fst ab) ∧ (Γ, (i', η)) ∈ R θ2 (snd ab)
      in
      on_ipair(fun Γ i i' η => env_ptr η ⊆ (key_set Γ) /\ condition Γ i i' η)
    end
  where "t_Rp( θ , d )" := (Primitives θ d).
  
  (** General realizers: the orthogonal closure of the primitive realizers *)
  Definition Realizers (a : type) (d : ty_denot a) : Ensemble RType
    := fun r => forall (d' : t_ty_denot a), d =-= eta d' -> r ∈ (Primitives a d') ⊥ ⊤.
  Arguments Realizers : clear implicits.

  Notation "Rp( θ , d )" := (Primitives θ d) (at level 70, no associativity).
  Notation "R( θ ,  d )" := (Realizers θ d) (at level 70, no associativity).
  
  (** Tests *)
  Definition Tests (a : type) (d : t_ty_denot a) : Ensemble TType
    := (Primitives a d) ⊥.
  Arguments Tests : clear implicits.

  Lemma tests_realizers:
    forall a (d : t_ty_denot a), Same_set _ (Tests a d) (Primitives a d ⊥ ⊤ ⊥).
  Proof.
    intros a d.
    change (Same_set _ (Tests a d) ((bbot ∘ btop ∘ bbot) (Primitives a d))).
    rewrite GF.comp_equality.
    unfold f.
    unfold Tests.
    reflexivity.
  Qed.
  
  Lemma primitive_Equal:
    forall Γ α a d d', d =-= d' ->
                  SetIn (Rp(a,d)) (Γ, α) ->
                  SetIn (Rp(a,d')) (Γ, α).
  Proof.
    intros Γ α a d d' d_eq_d' pr.
    simpl in *. unfold SetIn, "∈" in *. destruct α. destruct a.
    destruct c ; try contradiction.
    destruct v ; try contradiction.
    apply pr.
    destruct c ; try contradiction.
    destruct v ; try contradiction.
    simpl. rewrite <- d_eq_d'.
    apply pr.
    destruct c ; try contradiction.
    destruct v ; try contradiction.
    simpl. split. apply pr. intros d0 Γ' α β H H0 H1 H2 p H3.
    unfold "∈". intros d'0 H4.
    rewrite <- d_eq_d' in H4.
    destruct pr.
    specialize (H6 d0 Γ' α β H H0 H1 H2 p H3 d'0 H4).
    auto.
    destruct c ; try contradiction.
    destruct v ; try contradiction.
    split. apply pr. split. unfold "∈".
    intros d'0 H. apply (snd pr). rewrite <- H.
    destruct d, d'. simpl.
    inversion d_eq_d'. inversion H0. inversion H1.  split. auto. auto.
    unfold "∈".
    intros d'0 H. apply (snd pr). rewrite <- H.
    destruct d, d'. simpl.
    inversion d_eq_d'. inversion H0. inversion H1.  split. auto. auto.
  Qed.

  Lemma primitive_realizer:
    forall Γ α a (d : t_ty_denot a),
      SetIn (Primitives a d) (Γ, α) ->
      SetIn (Realizers a (eta d)) (Γ, α).
  Proof.
    intros Γ α a d.
    intros r_in d' d_eq_d'.
    eapply extensive. apply vinj in d_eq_d'.
    eapply primitive_Equal. apply d_eq_d'. auto.
  Qed.

  (** Realizers of enviroments *)
  Fixpoint EnvRealizers (ctx : ctx) : ctx_denot ctx -> Ensemble EType :=
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
                           SetIn (EnvRealizers ctx ρ') (Γ, η) /\
                           exists α β, find p Γ = Some β /\
                                  HClos_to_MClos β = Some α /\
                                SetIn (Realizers a d) (Γ, α)
                         | _ => False
                         end
    end.

  Notation "Γα ▶ d" := (SetIn (Realizers _ d) Γα)
                       (at level 80, no associativity).
  Notation "Γη ◈ ρ" := (SetIn (EnvRealizers _ ρ) Γη)
                       (at level 80, no associativity).

  Definition GRealizers (c : ctx) (a : type)
             (d : ctx_denot c =-> ty_denot a) : Ensemble Code
    := fun i =>
        forall (Γ : Heap) (η : MEnv) (ρ : ctx_denot c),
          heap_wf Γ -> (Γ, η) ◈ ρ -> (Γ, (i , η)) ▶ d ρ
  .

  Definition clos_Realizers (c : ctx) (a : type)
             (d : ctx_denot c =-> ty_denot a) : Ensemble Code
    := fun i => ideal_closure (flip (@GRealizers c a) i) d.
  
  Ltac pattern_heap_conf :=
    match goal with
      [ |- SetIn _ (?Γ, _, _) ] => pattern Γ
    end.

  Ltac pattern_heap_realizer :=
    match goal with
      [ |- SetIn _ (?Γ, _) ] => pattern Γ
    end.

  Ltac heap_rewrite_conf H := pattern_heap_conf ; rewrite -> H.
  Ltac heap_rewrite_realizer H := pattern_heap_realizer ; rewrite -> H.

  Lemma fold_Realizer (θ : type) (d : ty_denot θ) :
      (λ r : RType, ∀ d' : t_ty_denot θ, d =-= eta d' → (Rp( θ, d') ⌶) r)
      =
      R( θ , d ).
  Proof. auto. Qed.

  Add Parametric Morphism α s : (fun Γ => SetIn Ω (Γ, α, s)) with
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

  Lemma realizer_in_Ω :
    forall Γ Δ α s a (d : t_ty_denot a),
      r_wf (Γ, α)
      -> t_wf (Δ, s)
      -> Γ ⋈ Δ
      -> (Γ, α) ▶ (eta d)
      -> SetIn (Tests _ d) (Δ, s)
      -> SetIn Ω (Γ ∪ Δ, α, s).
  Proof.
    intros Γ Δ α s a d wf1 wf2 J0 R0 H0.
    unfold SetIn, "∈", Realizers in R0.
    specialize (R0 d (tset_refl (eta d)) (Δ,s) H0).
    eapply R0 ; auto.
  Qed.

  Lemma Tests_Equal':
    forall Δ s a d d', d =-= d' ->
                  SetIn (Tests a d) (Δ, s) ->
                  SetIn (Tests a d') (Δ, s).
  Proof.
    intros Δ s a d d' d_eq_d' t [Γ α] t_in.
    apply t.
    eapply primitive_Equal. symmetry. apply d_eq_d'.
    auto.
  Qed.
 
  Lemma realizers_Equal':
    forall Γ α a d d', d =-= d' ->
                 SetIn (Realizers a d) (Γ, α) ->
                 SetIn (Realizers a d') (Γ, α).
  Proof.
    intros Γ α a d d' d_eq_d' r d'' d'_eq_d'' [Δ s] t_in.
    rewrite <- d_eq_d' in d'_eq_d''.
    specialize (r d'' d'_eq_d'').
    apply r. eapply Tests_Equal'. symmetry.
    auto. auto.
  Qed.

  Lemma clos_realizers_Equal:
    forall i c a d d', d =-= d' ->
                  SetIn (@clos_Realizers c a d) i ->
                  SetIn (@clos_Realizers c a d') i.
  Proof.
    intros i c a d d' d_eq_d' H.
    intros A ss chain_c down_c.    
    eapply down_c. rewrite <- d_eq_d'; auto.
    apply H; auto.
  Qed.
  
  Lemma realizers_Equal:
    forall Γ Δ α a d, Γ ≃ Δ -> SetIn (Realizers a d) (Γ, α) ->
                           SetIn (Realizers a d) (Δ, α).
  Proof.
    intros Γ Δ [i η] a d EQ I. intros d' d_eq_d'.
    intros (Γ'', s) I1 WF1 WF2 Hble.
    assert (Δ ∪ Γ'' ≃ Γ ∪ Γ'') as EQ'.
    eapply Equal_join_mor.
    auto.
    symmetry.
    auto.
    reflexivity.
    pattern (Δ ∪ Γ''). rewrite -> EQ'.
    eapply realizer_in_Ω.
    split.
    rewrite EQ.
    eapply WF1.
    rewrite EQ.
    eapply WF1.
    auto.
    rewrite EQ.
    auto. instantiate (1:=d'). intros d'' d'_eq_d''.
    rewrite <- d_eq_d' in d'_eq_d''. specialize (I d'' d'_eq_d'').
    apply I.
    eauto.
  Qed.

  Add Parametric Morphism a (d : ty_denot a) α :
    (fun Γ => SetIn (Realizers a d) (Γ, α)) with
      signature Equal ==> iff as realizer_heap_mor.
  Proof.
    intros Γ Δ EQ.
    split ;
    eapply realizers_Equal ;
    auto.
    symmetry.
    auto.
  Qed.
  
  Lemma primitives_Equal:
    forall Γ Δ α a d, Γ ≃ Δ ->
                 SetIn (Primitives a d) (Γ, α) -> SetIn (Primitives a d) (Δ, α).
  Proof.
    intros Γ Δ α a d EQ I.
    destruct α as [i η].
    destruct a as [ | | a1 a2 | a1 a2].
    - (* Unit *)
      destruct i ; try contradiction.
      destruct v ; try contradiction.
      unfold SetIn, "∈". simpl.
      rewrite <- EQ. auto.
    - (* Int *)
      destruct i ; try contradiction.
      destruct v ; try contradiction.
      unfold SetIn, "∈". simpl.
      rewrite <- EQ. auto.
    - (* Grab *)
      rename d into f.
      destruct i ; try contradiction.
      destruct v ; try contradiction.
      cbn.
      destruct I as [H  D].
      split.
      rewrite <- EQ.
      auto.
      intros d Γ' [i' η'] hc H0 [H1 H2] H3 mclos_to_hclos p H4.
      cbv in mclos_to_hclos. rewrite <- mclos_to_hclos in *.
      assert (Δ ⋈ ⎨ p ⤇ (C i', η') ⎬) as E0.
      destruct_join_joinable.
      eauto.
      assert (Γ ⋈ ⎨ p ⤇ (C i', η') ⎬) as E1.
      destruct_join_joinable.
      rewrite EQ. auto.
      assert (Γ' ⋈ ⎨ p ⤇ (C i', η') ⎬) as E2.
      destruct_join_joinable.
      auto.
      assert (add p (C i', η') (Δ ∪ Γ') ≃ add p (C i', η') (Γ ∪ Γ')) as EQ'.
      repeat rewrite <- Join_add ; eauto.
      repeat rewrite Join_assoc_1 ; eauto.
      eapply Equal_join_mor ; eauto.
      symmetry. auto.
      reflexivity.
      rewrite <- EQ in H3 ; eauto.
      eapply realizers_Equal. symmetry. apply EQ'.
      eapply D ; eauto.
      split.
      auto.
      eapply H2.
      rewrite <- EQ in H3.
      auto.
    - (* Pair *)
      destruct i ; try contradiction.
      destruct v ; try contradiction.
      destruct I as [H [D1 D2]].
      split.
      rewrite <- EQ.
      auto.
      split. rewrite -> fold_Realizer in *.
      match goal with
      | [ |- (?Γ, ?i) ∈ R(a1, fst d)] =>
        change (SetIn (Realizers a1 (fst d)) (Γ, i)) ;
          pattern Γ
      end.
      rewrite <- EQ. apply D1.
      rewrite -> fold_Realizer in *.
      match goal with
      | [ |- (?Γ, ?i) ∈ R(a2, snd d)] =>
        change (SetIn (Realizers a2 (snd d)) (Γ, i)) ;
          pattern Γ
      end.
      rewrite <- EQ. apply D2.
  Qed.
  
  Add Parametric Morphism a (d : t_ty_denot a) α :
    (fun Γ => SetIn (Primitives a d) (Γ, α)) with
      signature Equal ==> iff as primitive_heap_mor1.
  Proof.
    intros Γ Δ EQ.
    split ;
    eapply primitives_Equal ;
    auto.
    symmetry.
    auto.
  Qed.

  Lemma env_realizers_Equal:
    forall c η ρ Γ Δ , Γ ≃ Δ ->
                  SetIn (EnvRealizers c ρ) (Γ, η) ->
                  SetIn (EnvRealizers c ρ) (Δ, η).
  Proof.
    induction c.
    intros η ρ Γ Δ EQ Her0.
    destruct ρ.
    destruct η ; try contradiction.
    auto.
    intros η ρ Γ Δ EQ Her1.
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
    
  Add Parametric Morphism c (ρ : ctx_denot c) η :
    (fun Γ => SetIn (EnvRealizers c ρ) (Γ, η)) with
      signature Equal ==> iff as env_realizer_heap_mor.
  Proof.
    intros Γ Γ' EQ.
    split ;
      eapply env_realizers_Equal ;
      eauto.
    symmetry.
    auto.
  Qed.

  Lemma Tests_Equal:
    forall Γ Δ s a d, Γ ≃ Δ -> SetIn (Tests a d) (Γ, s) -> SetIn (Tests a d) (Δ, s).
  Proof.
    intros Γ Δ s a d EQ I.
    intros (Γ'', [i η]) I1.
    intros Hwf0 Hwf1 Hble.
    assert (Γ'' ∪ Δ ≃ Γ'' ∪ Γ) as EQ'.
    eapply Equal_join_mor.
    auto.
    reflexivity.
    symmetry. auto.
    pattern (Γ'' ∪ Δ). rewrite -> EQ'.
    eapply realizer_in_Ω.
    split.
    eauto.
    eapply Hwf0.
    split.
    rewrite EQ.
    eapply Hwf1.
    rewrite EQ.
    eapply Hwf1.
    rewrite EQ.
    auto.
    eapply primitive_realizer ; eauto.
    auto.
  Qed.

  Add Parametric Morphism a (d : t_ty_denot a) α :
    (fun Γ => SetIn (Tests a d) (Γ, α)) with
      signature Equal ==> iff as tests_heap_mor.
  Proof.
    intros Γ Δ EQ.
    split ;
      eapply Tests_Equal ;
      eauto.
    symmetry.
    auto.
  Qed.

  Lemma env_realizer_ptr:
    forall ctx (ρ : ctx_denot ctx) η Γ,
      (Γ, η) ◈ ρ -> Included _ (env_ptr η) (key_set Γ).
  Proof.
    induction ctx ;
    intros ρ η Γ Her0.
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

  Lemma realizer_extend_heap:
    forall Γ Δ α a (d : ty_denot a),
      r_wf (Γ, α) -> Γ ⋈ Δ -> (Γ, α) ▶ d -> (Γ ∪ Δ, α) ▶ d.
  Proof.
    intros Γ Δ α a d Hwf Hjble H0. intros d' d_eq_d'.
    intros (Δ', s) H1.
    intros Hwf1 Hwf2 Hjble2.
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
    eapply realizer_in_Ω ; auto.
    eapply realizers_Equal'. apply d_eq_d'.
    auto. auto.
  Qed.
       
  Lemma env_realizer_nil:
    forall Γ η (ρ : ctx_denot nil), (Γ, η) ◈ ρ -> η = nil.
  Proof.
    intros Γ η ρ H.
    simpl in H.
    destruct η.
    auto.
    contradict H.
  Qed.

  Lemma bot_approx : forall θ Γ α,
      SetIn (Realizers θ PBot) (Γ, α).
  Proof.
    intros θ Γ α.
    intros pbot pbot_eq_eta.
    symmetry in pbot_eq_eta.
    apply PBot_incon_eq in pbot_eq_eta.
    contradiction.
  Qed.

  Lemma g_bot_approx : forall θ c i,
      SetIn (@GRealizers c θ (const _ PBot)) i.
  Proof.
    intros θ c i Γ η ρ Hwf Her.
    intros pbot pbot_eq_eta.
    symmetry in pbot_eq_eta.
    apply PBot_incon_eq in pbot_eq_eta.
    contradiction.
  Qed.
  
  Lemma env_realizer_def:
    forall (c : ctx) Γ η (ρ : ctx_denot c) α β a (d : ty_denot a) q,
      find q Γ = Some β ->
      HClos_to_MClos β = Some α ->
      (Γ, α) ▶ d -> 
      (Γ, η) ◈ ρ  ->
      (Γ, q :: η) ◈ ((d, ρ) : ctx_denot (a :: c)).
  Proof.
    intros c Γ η ρ α β a d q F H Hr Henv.
    split. auto.
    exists α, β. split ; auto.
  Qed.
    
  Lemma env_realizer_extend_heap: forall (c : ctx) Γ Δ η (ρ : ctx_denot c),
      heap_wf Γ -> Γ ⋈ Δ -> (Γ, η) ◈ ρ -> (Γ ∪ Δ, η) ◈ ρ.
  Proof.
    induction c.
    - intros Γ Δ η ρ wf H1 H2.
      destruct ρ.
      set (Q := env_realizer_nil _ _ _ H2).
      clearbody Q.
      rewrite Q in H2.
      rewrite Q.
      auto.
    - intros Γ Δ η ρ wf H1 H2.
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
    forall Γ Γ' α β a (d : ty_denot a) c (ρ : ctx_denot c) η q,
      heap_wf Γ ->
      HClos_to_MClos β = Some α ->
      r_wf (Γ', α) ->
      Γ ⋈ Γ' ->
      (Γ ∪ Γ') ⋈ ⎨ q ⤇ β ⎬ ->
      (Γ, η) ◈ ρ ->
      (Γ', α) ▶ d ->
      (Γ ∪ Γ' ∪ ⎨ q ⤇ β ⎬, q :: η) ◈ ((d, ρ) : ctx_denot (a :: c)).
  Proof.
    intros Γ Γ' α β a d c ρ η q Hwf0 β_to_α Hwf1 Hjble0 Hjble1 Her0 Hr0.
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

  Lemma tests_functional:
    forall Γ Δ α β s a b (d : ty_denot a) (f : t_ty_denot (a ⇾ b)) fd p,
      HClos_to_MClos β = Some α ->
      r_wf (Γ, α) ->
      t_wf (Δ, s) ->
      Γ ⋈ Δ ->
      (Γ ∪ Δ) ⋈ ⎨ p ⤇ β ⎬ ->
      (Γ, α) ▶ d ->
      f d =-= eta fd ->
      SetIn (Tests b fd) (Δ, s) ->
      SetIn (Tests _ f) (Γ ∪ Δ ∪ ⎨ p ⤇ β ⎬, ⌑ p :: s).
  Proof.
    intros Γ Δ α β s a b d f fd p.
    intros β_to_α Hwf0 Hwf1 Hjble0 Hjble1 Hr0 fd_eq Ht0.
    intros (Γ'', α') Hp0.
    intros Hwf2 Hwf3 Hjble2.
    set (Γ' := Γ ∪ Δ ∪ (⎨ p ⤇ β ⎬)).
    fold Γ' in Hjble2.
    destruct α' as [i0 η].
    destruct i0 ; try contradiction.
    destruct v ; try contradiction.
    destruct Hp0 as [Hinc0 Hgrab].
    assert (Γ'' ⋈ Γ) as Hjble3.
    - Case "Γ'' ⋈ Γ".
      apply joinable_comm; apply Joinable_join_elim_1 with (Δ:= Δ ∪ (⎨ p ⤇ β ⎬)).
      eapply Joinable_join_intro_r. auto.
      apply Joinable_join_elim_1 with (Δ:=Δ). auto. auto.
      rewrite <- Join_assoc_1; auto.
      apply Joinable_join_elim_1 with (Δ:=Δ); auto.
      apply Joinable_join_elim_2 with (Γ:=Γ); auto.
    assert (Γ'' ∪ Γ ⋈ ⎨ p ⤇ β ⎬) as Hjble4.
    - Case "Γ'' ∪ Γ ⋈ ⎨ p ⤇ β ⎬".
      apply Joinable_join_intro_l.
      apply joinable_comm; apply Joinable_join_elim_2 with (Γ:= Γ ∪ Δ); auto.
      apply Joinable_join_elim_1 with (Δ:=Δ); auto.
    apply HClos_prop in β_to_α.
    specialize (Hgrab d Γ α β Hr0 Hwf0 Hjble3 β_to_α p Hjble4).
    eapply antiex. econstructor.
    set (Δ' := Γ'' ∪ Γ ∪ (⎨ p ⤇ β ⎬)).
    assert (Γ'' ⋈ Δ) as E0.
    - Case "Γ'' ⋈ Δ".
      unfold Γ' in *.
      rewrite -> Join_comm_1 in Hjble2.
      rewrite <- Join_assoc_1 in Hjble2 ; auto.
      rewrite -> joinable_comm in Hjble2 ; auto.
      rewrite joinable_comm; apply Joinable_join_elim_2
                               with (Γ:= (⎨ p ⤇ β ⎬) ∪ Γ).
      apply Joinable_join_intro_l.
      rewrite joinable_comm;
        apply Joinable_join_elim_2 with (Γ:=Γ); auto. auto. auto.
      rewrite joinable_comm;
        apply Joinable_join_elim_1 with (Δ:=Δ). auto. auto.
      rewrite joinable_comm;
        apply Joinable_join_elim_2 with (Γ:=Γ); auto. auto.
    assert (Γ'' ∪ Γ' ≃  Δ' ∪ Δ) as E.
    - Case "Γ'' ∪ Γ' ≃  Δ' ∪ Δ".
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
    apply realizer_in_Ω with (d := fd).
    destruct_join_joinable.
    assert (Γ'' ⋈ ⎨ p ⤇ β ⎬) as Hjble5; auto.
    assert (Γ ⋈ ⎨ p ⤇ β ⎬) as Hjble6; auto.
    assert (Same_set _ (key_set (⎨ p ⤇ β ⎬)) (Singleton _ p)) as R.
    - Case "(key_set (⎨ p ⤇ β ⎬) = { p }".
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
    transitivity (key_set Γ''); auto.
    eapply Included_Union_1.
    rewrite <- Included_Singleton.
    rewrite Union_comm.
    transitivity (key_set (⎨ p ⤇ β ⎬)).
    rewrite R.
    reflexivity.
    eapply Included_Union_1.
    auto. auto.
    auto.
    unfold Δ'.
    eapply Joinable_join_intro_l ; eauto.
    rewrite joinable_comm.
    eapply Joinable_join_elim_2.
    eapply Hjble0; auto. auto.
    assert (Δ' ≃ add p β (Γ'' ∪ Γ)) as E'.
    unfold Δ'.
    eapply Join_add. auto.
    heap_rewrite_realizer E'.
    eapply realizers_Equal'. apply fd_eq.
    apply Hgrab.
    auto.
  Qed.

  Lemma env_realizer_lookup:
    forall n Γ η ctx (ρ : ctx_denot ctx) a,
    forall Q : nth_error ctx n = Some a,
      (Γ, η) ◈ ρ -> 
      exists p, nth_error η n = Some p /\
           exists α β, find p Γ = Some β
                  /\ HClos_to_MClos β = Some α
                  /\ (Γ, α) ▶ (lookup_nat _ _ Q ρ).
  Proof.
    induction n ;
    intros Γ η ctx ρ a Q Hr0.
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

  Lemma realizer_access:
    forall Γ η ctx a (ρ : ctx_denot ctx) n,
      forall Q:  nth_error ctx n = Some a,
        (Γ, η) ◈ ρ ->
        (Γ, (iaccess n, η)) ▶ lookup_nat _ _ Q ρ.
  Proof.
    intros Γ η ctx a ρ n Q Her0.
    set (d := lookup_nat n ctx Q ρ). intros d' d_eq_d'.
    intros (Δ, s) Ht0.
    intros Hwf1 Hwf2 Hjble.
    set (H := env_realizer_lookup _ _ _ _ _ Q Her0).
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
    eapply r_wf_find. apply Hwf1.
    eauto.
    auto.
    auto.
    eauto. eapply realizers_Equal'. apply d_eq_d'. apply Hr2.
    auto.
  Qed.

  Lemma realizer_push:
    forall Γ i η ctx a b (ρ : ctx_denot ctx) n (f : ty_denot (a ⇾ b)),
      forall Q:  nth_error ctx n = Some a,
        (Γ, η) ◈ ρ ->
        (Γ, (i, η)) ▶ f ->
        (Γ, (ipush n i, η)) ▶ AppTy_ρ f (lookup_nat _ _ Q ρ).
  Proof.
    intros Γ i η ctx a b ρ n f Q Her0 Hr0.
    set (d := lookup_nat _ _ Q ρ). intros fd f_eq_fd.
    intros (Δ, s) Ht0.
    intros Hwf1 Hwf2 Hjble.
    set (H := env_realizer_lookup _ _ _ _ _ Q Her0).
    clearbody H.
    destruct H  as [q [EQ EX]].
    destruct EX as [α [β [F1 [? Hr2]]]].
    eapply antiex.
    econstructor.
    exact EQ.
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
    apply AppTyValVal in f_eq_fd. inversion f_eq_fd as [f' [f_eq_f' d_eq_fd]].
    eapply realizer_in_Ω.
    split. apply Hwf1. apply Hwf1.
    split.
    eapply wf_union ; eauto.
    rewrite Join_key_set.
    eapply stack_ptr_cons_included.
    transitivity (key_set Δ).
    eapply Hwf2.
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
    auto.
    eapply realizers_Equal'. apply f_eq_f'. auto.
    assert (Γ ∪ Δ ≃ Γ ∪ Δ ∪ (⎨ q ⤇ β ⎬)) as E2.
    eapply find_singleton_Join.
    eapply find_submap.
    eapply join_sub1.
    auto. auto.
    heap_rewrite_realizer E2.
    eapply tests_functional. apply H.
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
    eauto.
    exact Hr2.
    apply d_eq_fd.
    auto.
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

  (** We need an extra requirement for PointerType: given any finite set
      of pointers, we
      need to be able to pick a fresh pointer that is not in the set.
   *)
  (* @todo: I think that to properly formalize this we need to prove
     that every Ensemble set used here is Ensembles.Finite and then
     use MSetsToFiniteSets library (this is a huge ton of work) *)
  Definition exists_fresh_pointer := forall Γ η s, exists p, fresh_for p Γ η s.
  
  (* Lemma 5.21. *)
  Lemma tests_pairs_1 :
    forall Γ Δ s θ1 θ2
      (d1 : t_ty_denot θ1) (d2 : ty_denot θ2) (d1d2 : t_ty_denot (θ1 ⨱ θ2)),
    t_wf (Δ, s) ->
    Γ ⋈ Δ ->
    d1d2 =-= (eta d1, d2) ->
    SetIn (Tests θ1 d1) (Δ, s) ->
    SetIn (Tests (θ1 ⨱ θ2) d1d2) (Γ ∪ Δ, mapplypi1 :: s).
  Proof.
    intros Γ Δ s θ1 θ2 d1 d2 d1d2 Her Hjble d1d2_eq ΔsTest.
    intros (Γ', α')  approx' Hwf' Her' Hjble'.
    destruct α' as [i η].
    destruct i ; try contradiction.
    destruct v ; try contradiction. rename c into i; rename c0 into i'.
    eapply antiex. constructor.
    destruct approx' as [H [H1 H2]]. rewrite -> fold_Realizer in H1,H2.
    assert (FST _ _ d1d2 =-= eta d1).
    - (* assert *)
      fold t_ty_denot. rewrite -> d1d2_eq.
      by simpl. fold t_ty_denot in H0.
    eapply realizers_Equal' in H1. 2 : { apply H0. } clear H0.
    specialize (H1 _ (tset_refl (eta d1)) _ ΔsTest). simpl in H1.
    simpl in *. destruct Hwf'.
    apply joinable_comm in Hjble'.
    have ble := Joinable_join_elim_2 Hjble Hjble'.
    have bla := Joinable_join_elim_1 Hjble Hjble'.
    destruct Her.
    assert (Γ' ∪ (Γ ∪ Δ) ≃ (Γ' ∪ Δ) ∪ Γ) as E.
    - (* Assert *)
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
    Qed.

  Lemma tests_pairs_2 :
    forall Γ Δ s θ1 θ2
      (d1 : ty_denot θ1) (d2 : t_ty_denot θ2) (d1d2 : t_ty_denot (θ1 ⨱ θ2)),
    t_wf (Δ, s) ->
    Γ ⋈ Δ ->
    d1d2 =-= (d1, eta d2) ->
    SetIn (Tests θ2 d2) (Δ, s) ->
    SetIn (Tests (θ1 ⨱ θ2) d1d2) (Γ ∪ Δ, mapplypi2 :: s).
  Proof.
    intros Γ Δ s θ1 θ2 d1 d2 d1d2 Her Hjble d1d2_eq ΔsTest.
    intros (Γ', α')  approx' Hwf' Her' Hjble'.
    destruct α' as [i η].
    destruct i ; try contradiction.
    destruct v ; try contradiction. rename c into i; rename c0 into i'.
    eapply antiex. constructor.
    destruct approx' as [H [H1 H2]]. rewrite -> fold_Realizer in H1,H2.
    assert (SND _ _ d1d2 =-= eta d2).
    - (* assert *)
      fold t_ty_denot. rewrite -> d1d2_eq.
      by simpl. fold t_ty_denot in H0.
    eapply realizers_Equal' in H2. 2 : { apply H0. } clear H0.  
    specialize (H2 _ (tset_refl (eta d2)) _ ΔsTest). simpl in H2.
    simpl in *. destruct Hwf'.
    apply joinable_comm in Hjble'.
    have ble := Joinable_join_elim_2 Hjble Hjble'.
    have bla := Joinable_join_elim_1 Hjble Hjble'.
    destruct Her.
    assert (Γ' ∪ (Γ ∪ Δ) ≃ (Γ' ∪ Δ) ∪ Γ) as E.
    - (* Assert *)
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
  Qed.

  Lemma tests_bop_1:
    ∀ (bop : BOp) (Γ Γ': Heap) (i' : Code) (η η' : MEnv)
      (m m' : int_cpoType) (Δ : Heap) (s : stack) (p : Pointer),
      fresh_for_heap p (Γ ∪ Δ) ->
      r_wf (Γ', (ival (iint m%Z), η')) ->
      t_wf (Δ, s) ->
      Γ ⋈ Δ ->
      Γ' ⋈ Map.add p (K (ZBOpL i'), η) (Γ ∪ Δ) -> (* Γ' ⋈ Δ *)
      (Δ, s) ∈ (Rp( tint, semZBOp bop m m')) ⊥ ->
      SetIn (Tests tint m')
            (Map.add p (K (ZBOpR (iint m)), η') (Γ' ∪ Δ), bopapply p bop :: s).
  Proof.
    intros bop Γ Γ' i' η η' m m' Δ s p p_fresh Γ'wf Δwf Γ_Δ Γ'_ΓΔp Δtests.
    intros [Γ'' [im η'']] r_m' Γ''wf Γ'Δpwf Γ''_Γ'Δp.
    destruct im ; try contradiction.
    destruct v ; try contradiction.
    destruct r_m'.
    eapply antiex. apply tbop_apply_3.
    apply heap_find_join_prop'. auto. right.
    apply F.add_eq_o. auto.
    assert(Γ'_Δ : Γ' ⋈ Δ).
      --  apply Join_fresh_add_prop in Γ'_ΓΔp.
          apply joinable_comm.
          eapply Joinable_join_elim_2. apply Γ_Δ. auto. apply p_fresh.
    assert (as0 : Γ'' ∪ Map.add p (K (ZBOpR (iint m)), η') (Γ' ∪ Δ)
                          ≃
                  (Γ'' ∪ Map.add p (K (ZBOpR (iint m)), η') Γ') ∪ Δ
           ).
    - (* begin as0 *)
      apply fresh_for_heap_join in p_fresh.
      rewrite -> Equal_join_mor.
      2 : { auto. } 2 : { reflexivity. }
      2 : { rewrite <- heap_add_join_prop'.
            rewrite Join_comm_1.
            rewrite heap_add_join_prop.
            rewrite Join_comm_1.
            reflexivity.
            apply joinable_comm.
            apply Join_add_prop'. apply p_fresh. auto.
            apply p_fresh. auto.
            apply Join_add_prop''. auto. auto.
      }
      2 : { auto. }
      rewrite <- Join_comm_1 in Γ''_Γ'Δp. 2 : { auto. }
      rewrite <- heap_add_join_prop' in Γ''_Γ'Δp. 2 : { auto. }
      rewrite <- Join_assoc_1. reflexivity.
      apply comp_join_elim_r with (Δ:=add p (K (ZBOpR (iint m)), η') Δ).
      apply Join_add_prop''. auto. auto.
      2 : { apply Join_add_prop. apply Joinable_fresh. apply p_fresh. auto. }
      apply comp_join_elim_l with (Σ:=add p (K (ZBOpR (iint m)), η') Γ').
      apply joinable_comm.
      apply Join_add_prop'. apply p_fresh. auto.
      rewrite <- heap_add_join_prop. auto. apply p_fresh. auto.
  (* end as0 *)
  heap_rewrite_conf as0.
  unfold "∈", "⊥", "⊧", satif in Δtests.
  assert (as1 : (Γ'' ∪ Map.add p (K (ZBOpR (iint m)), η') Γ',
                 (ival (iint (semZBOp bop m m')), η'))
                  ∈
                  Rp( tint, semZBOp bop m m')).
  - (* begin as1 *)
    split. rewrite Join_key_set.
    intros q q_in. apply Union_intror.
    apply F.add_in_iff. right. apply Γ'wf. auto.
    rewrite <- Join_comm_1 in Γ''_Γ'Δp. 2 : { auto. }
    rewrite <- heap_add_join_prop' in Γ''_Γ'Δp. 2 : { auto. }
    apply comp_join_elim_r with (Δ:=add p (K (ZBOpR (iint m)), η') Δ).
    apply Join_add_prop''. auto. auto. auto.
  (* end as1 *)
  specialize (Δtests _ as1). do 2 destruct H0.
  apply Δtests.
  unfold r_wf. split.
  apply wf_union.
  rewrite <- Join_comm_1 in Γ''_Γ'Δp. 2 : { auto. }
  rewrite <- heap_add_join_prop' in Γ''_Γ'Δp. 2 : { auto. }
  apply comp_join_elim_r with (Δ:=add p (K (ZBOpR (iint m)), η') Δ).
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
  apply comp_join_elim_l with (Σ:=add p (K (ZBOpR (iint m)), η') Γ').
  apply joinable_comm.
  apply Join_add_prop'. apply p_fresh.
  auto. rewrite <- heap_add_join_prop. auto. apply p_fresh. auto.
  apply Join_add_prop'. apply p_fresh. auto.
  Qed.
  
  Lemma tests_bop_2:
    ∀ (bop : BOp) (Γ : Heap) (i i' : Code) (η : MEnv) (m m' : t_ty_denot tint)
      (Δ : Heap) (s : stack) (p : Pointer),
      fresh_for_heap p (Γ ∪ Δ) ->
      (Γ, (i', η)) ▶ (eta m') ->
      (Δ, s) ∈ (Rp( tint, semZBOp bop m m')) ⊥ ->
      r_wf (Γ, (ibop bop i i', η)) ->
      t_wf (Δ, s) ->
      Γ ⋈ Δ ->
      SetIn (Tests tint m)
            (Map.add p (K (ZBOpL i'), η) (Γ ∪ Δ), bopapply p bop :: s).
  Proof.
    intros bop Γ i i' η m m' Δ s p p_fresh r_i' t_Δ Γwf Δwf Γ_Δ.
    intros [Γ' [im η']] r_m Γ'wf ΓΔpwf Γ'_ΓΔp.
    destruct im ; try contradiction.
    destruct v ; try contradiction.
    destruct r_m.
    eapply antiex. apply tbop_apply_2.
    apply heap_find_join_prop'. auto. right.
    apply F.add_eq_o. auto.
    assert (as0 : Map.add p (K (ZBOpR (iint m)), η')
                            (Γ' ∪ Map.add p (K (ZBOpL i'), η) (Γ ∪ Δ))
                            ≃
                  Γ ∪ (Map.add p (K (ZBOpR (iint m)), η') (Γ' ∪ Δ))
           ).
    - (* begin as0 *)
      assert(Γ'_Γ : Γ' ⋈ Γ).
      --  apply Join_fresh_add_prop in Γ'_ΓΔp.
          apply joinable_comm.
          eapply Joinable_join_elim_2.
          apply joinable_comm. apply Γ_Δ.
          rewrite Join_comm_1. auto. auto. apply p_fresh.
      assert(Γ'_Δ : Γ' ⋈ Δ).
      --  apply Join_fresh_add_prop in Γ'_ΓΔp.
          apply joinable_comm.
          eapply Joinable_join_elim_2. apply Γ_Δ. auto. apply p_fresh.
      rewrite <- heap_add_join_prop'. 2 : { auto. }
      rewrite -> Equal_join_mor.
      2 : { apply Join_add_prop''. auto. }
      2 : { reflexivity. }
      2 : { rewrite heap_add_update_prop. reflexivity. }
      rewrite -> Equal_join_mor.
      2 : { apply Join_add_prop''. apply Join_fresh_add_prop in Γ'_ΓΔp.
            auto. apply p_fresh.
      }
      2 : { reflexivity. }
      2 : { rewrite <- heap_add_join_prop'. reflexivity. auto. }
      rewrite <- Join_assoc_1.
      rewrite -> Equal_join_mor.
      2 : { rewrite Join_comm_1.
            rewrite -> heap_add_join_prop'.
            apply Join_add_prop''. apply Joinable_join_intro_l. auto. auto. auto.
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
  do 2 destruct H0. clear H1. heap_rewrite_conf as0.
  assert (as1 : SetIn (Tests tint m')
            (Map.add p (K (ZBOpR (iint m)), η') (Γ' ∪ Δ), bopapply p bop :: s)).
  eapply tests_bop_1. apply p_fresh. auto. auto.
  auto. apply Γ'_ΓΔp. auto.
  specialize (r_i' m' (tset_refl (eta m')) _ as1).
  unfold "⊧", satif in r_i'.
  apply r_i'. auto.
  split. split.
  intros q q_in. destruct q_in. auto.
  destruct H0 as [k [? [? [? ?]]]].
  apply F.add_mapsto_iff in H0. destruct H0. destruct H0.
  apply F.add_in_iff. inversion H2. right.
  apply join_in1. apply Γ'wf. rewrite <- H5 in *. apply H1.
  destruct H0.
  apply F.add_in_iff. right.
  apply join_MapsTo in H2. destruct H2.
  apply join_in1. destruct Γ'wf. apply H3.
  apply Union_intror. exists k, x0, x1. auto.
  apply join_in2. destruct Δwf. apply H3.
  apply Union_intror.  exists k, x0, x1. auto.
  intros q q_in. apply Union_introl. auto.
  intros q q_in.
  destruct q_in. inversion H0. inversion H1.
  apply F.add_in_iff. right.
  apply join_in2. apply Δwf. left. apply H1.
  inversion H0. inversion H1. inversion H2.
  apply F.add_in_iff. right.
  apply join_in2. apply Δwf. right. left. apply H2.
  inversion H1. inversion H2. inversion H3.
  apply F.add_in_iff. right.
  apply join_in2. apply Δwf. right. right. left. apply H3.
  inversion H2. inversion H3. inversion H4.
  apply F.add_in_iff. right.
  apply join_in2. apply Δwf. right. right. right. left. apply H4.
  inversion H3. inversion H4. inversion H5. inversion H6.
  apply F.add_in_iff. left. auto.
  apply F.add_in_iff. right.
  apply join_in2. apply Δwf. right. right. right. right. left. exists x. auto.
  inversion H4. inversion H5.
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

  Lemma tests_bop_3 :
    forall bop Γ i i' η (m m' : t_ty_denot tint),
      exists_fresh_pointer ->
      SetIn (Realizers tint (eta m)) (Γ, (i,η)) ->
      SetIn (Realizers tint (eta m')) (Γ, (i',η)) ->
      SetIn (Primitives tint (semZBOp bop m m'))⊥⊤ (Γ, (ibop bop i i', η)).
  Proof.
    intros bop Γ i i' η m m' p_fresh r_i r_i'.
    intros [Δ s] t_Δ Γwf Δwf Γ_Δ.
    destruct p_fresh with (Γ:=(Γ ∪ Δ)) (η:=η) (s:=s) as [p].
    eapply antiex. constructor. apply H.
    assert (as0 : SetIn (Tests tint m)
                    (Map.add p (K (ZBOpL i'), η) (Γ ∪ Δ), bopapply p bop :: s)).
    eapply tests_bop_2.
    destruct H. auto. apply r_i'.
    auto. apply Γwf.
    auto. auto.
    specialize (r_i m (tset_refl (eta m)) _ as0).
    unfold "⊧", satif in r_i.
    assert (as1 : Γ ∪ Map.add p (K (ZBOpL i'), η) (Γ ∪ Δ) ≃
                    Map.add p (K (ZBOpL i'), η) (Γ ∪ Δ)).
    - (* as1 *)
      destruct H.
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
    apply r_i. apply Γwf.
    split. split.
    intros q q_in. destruct q_in. auto.
    destruct H0 as [k [? [? [? ?]]]].
    apply F.add_mapsto_iff in H0. destruct H0. destruct H0.
    apply F.add_in_iff. inversion H2. right.
    apply join_in1. apply Γwf. rewrite <- H5 in *. apply H1.
    destruct H0.
    apply F.add_in_iff. right.
    apply join_MapsTo in H2. destruct H2.
    apply join_in1. destruct Γwf. apply H3.
    apply Union_intror. exists k, x0, x1. auto.
    apply join_in2. destruct Δwf. apply H3.
    apply Union_intror.  exists k, x0, x1. auto.
    intros q q_in. apply Union_introl. auto.
    intros q q_in.
    destruct q_in. inversion H0. inversion H1.
    apply F.add_in_iff. right.
    apply join_in2. apply Δwf. left. apply H1.
    inversion H0. inversion H1. inversion H2.
    apply F.add_in_iff. right.
    apply join_in2. apply Δwf. right. left. apply H2.
    inversion H1. inversion H2. inversion H3.
    apply F.add_in_iff. right.
    apply join_in2. apply Δwf. right. right. left. apply H3.
    inversion H2. inversion H3. inversion H4.
    apply F.add_in_iff. right.
    apply join_in2. apply Δwf. right. right. right. left. apply H4.
    inversion H3. inversion H4. inversion H5. inversion H6.
    apply F.add_in_iff. left. auto.
    apply F.add_in_iff. right.
    apply join_in2. apply Δwf. right. right. right. right. left. exists x. auto.
    inversion H4. inversion H5.
    apply F.add_in_iff. right.
    apply join_in2. apply Δwf. right. right. right. right. right. auto.
    apply joinable_comm.
    apply Join_add_prop'. destruct H.
    apply (fresh_for_heap_join Γ_Δ H).
    apply Joinable_join_intro_l. apply Joinable_refl.
    auto.
  Qed.

  Lemma ifz_conf_prop : forall Γ Γ' Δ α i i' p η s,
      fresh_for_heap p (Γ ∪ Δ) ->
      r_wf (Γ, (i, η)) ->
      t_wf (Δ, s) ->
      Γ ⋈ Δ ->
      Γ' ⋈ Map.add p (α, η) (Γ ∪ Δ) ->
      SetIn Ω (Γ ∪ Δ, (i', η), s) ->
      SetIn Ω (Γ' ∪ Map.add p (α, η) (Γ ∪ Δ), (i', η), s).
  Proof.
    intros Γ Γ' Δ α i i' p η s p_fresh Γwf Δwf Γ_Δ Γ'_pΓΔ w_in.
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
    ∀ (Γ Δ : Heap) (η : MEnv) (θ : type) (i i' i'' : Code)
      (d : t_ty_denot tint) (d' d'' : ty_denot θ) (s : stack) (p : Pointer)
      (ifzv : t_ty_denot θ),
      fresh_for_heap p (Γ ∪ Δ) ->
      (Γ, (i', η)) ▶ d' ->
      (Γ, (i'', η)) ▶ d'' ->
      r_wf (Γ, (iifz i i' i'', η)) ->
      t_wf (Δ, s) ->
      Γ ⋈ Δ ->
      IfZSemInt d' d'' d =-= eta ifzv ->
      (Δ, s) ∈ (Rp( θ, ifzv)) ⊥ ->
      SetIn (Tests tint d) (Map.add p (K (IfZ i' i''), η) (Γ ∪ Δ), ? p :: s).
  Proof.
    intros Γ Δ η θ i i' i'' d d' d'' s p ifzv p_fresh
           r_i' r_i'' Γwf Δwf Γ_Δ ifz_is_eta Δtests.
    intros [Γ' [id η']] r_Γ' Γ'wf ΓpΔwf Γ'_Δ.
    destruct id ; try contradiction.
    destruct v ; try contradiction.
    destruct z.
    - (* z = 0 *)
      eapply antiex. eapply tifz_0.
      apply heap_find_join_prop'. auto. right.
      apply F.add_eq_o. auto.
      eapply ifz_conf_prop. apply p_fresh. apply Γwf. auto. auto. auto.
      destruct r_Γ'. rewrite -> H0 in *. simpl in ifz_is_eta.
      specialize (r_i' ifzv ifz_is_eta _ Δtests). apply r_i'. auto. auto. auto.
    - (* z > 0 *)
      eapply antiex. eapply tifz_n0.
      apply heap_find_join_prop'. auto. right.
      apply F.add_eq_o. auto. intro pos_eq_Z0.
      inversion pos_eq_Z0.
      eapply ifz_conf_prop. apply p_fresh. apply Γwf. auto. auto. auto.
      destruct r_Γ'. rewrite -> H0 in *. simpl in ifz_is_eta.
      specialize (r_i'' ifzv ifz_is_eta _ Δtests). apply r_i''. auto.
      auto. auto.
    - (* z < 0 *)
      eapply antiex. eapply tifz_n0.
      apply heap_find_join_prop'. auto. right.
      apply F.add_eq_o. auto. intro neg_eq_Z0.
      inversion neg_eq_Z0.
      eapply ifz_conf_prop. apply p_fresh. apply Γwf. auto. auto. auto.
      destruct r_Γ'. rewrite -> H0 in *. simpl in ifz_is_eta.
      specialize (r_i'' ifzv ifz_is_eta _ Δtests). apply r_i''. auto.
      auto. auto.
  Qed.

  Lemma tests_ifz_Z :
    forall Γ η θ i i' i'' d' d'',
      exists_fresh_pointer ->
      SetIn (Realizers tint (eta 0%Z)) (Γ, (i,η)) ->
      SetIn (Realizers θ (eta d')) (Γ, (i',η)) ->
      SetIn (Realizers θ d'') (Γ, (i'',η)) ->
      SetIn (Primitives θ d')⊥⊤ (Γ, (iifz i i' i'', η)).
  Proof.
    intros Γ η θ i i' i'' d' d'' p_fresh r_i r_i' r_i''.
    intros [Δ s] t_Δ Γwf Δwf Γ_Δ.
    destruct p_fresh with (Γ:=(Γ ∪ Δ)) (η:=η) (s:=s) as [p].
    eapply antiex. constructor. apply H.
    assert (p_fresh_ΓΔηs:=H).
    destruct H. apply (fresh_for_heap_join Γ_Δ) in H.
    assert (as0 : add p (K (IfZ i' i''), η) (Γ ∪ Δ)
                          ≃
                  Γ ∪ add p (K (IfZ i' i''), η) (Γ ∪ Δ)
           ).
    - (* begin as0 *)
      symmetry.
      rewrite Join_comm_1. rewrite <- heap_add_prop_idemp'''. reflexivity.
      apply H. auto. auto. apply joinable_comm. apply Join_add_prop'. apply H.
      apply joinable_comm. apply joinable_join1. auto.
    (* end as0 *)
    assert (as1 : SetIn (Tests tint 0%Z)
                        (Map.add p (K (IfZ i' i''), η) (Γ ∪ Δ), ? p :: s)
           ).
    eapply tests_ifz. apply p_fresh_ΓΔηs.
    apply r_i'. apply r_i''. apply Γwf. auto. auto. simpl. auto. auto.
    heap_rewrite_conf as0.
    specialize (r_i 0%Z (tset_refl (eta 0%Z)) _ as1).
    apply r_i. auto.
    split. apply wf_add. apply wf_union. auto. apply Γwf. apply Δwf.
    intros q q_in. apply join_in1. apply Γwf. auto.
    apply stack_ptr_cons_included_if.
    intros q q_in. apply F.add_in_iff. right. apply join_in2. apply Δwf. auto.
    apply F.add_in_iff. left. auto.
    apply joinable_comm. apply Join_add_prop'. apply H.
    apply joinable_comm. apply joinable_join1. auto.
  Qed.

  Lemma tests_ifz_NZ :
    forall Γ η θ i i' i'' d d' d'',
      exists_fresh_pointer ->
      d <> 0%Z ->
      SetIn (Realizers tint (eta d)) (Γ, (i,η)) ->
      SetIn (Realizers θ d') (Γ, (i',η)) ->
      SetIn (Realizers θ (eta d'')) (Γ, (i'',η)) ->
      SetIn (Primitives θ d'')⊥⊤ (Γ, (iifz i i' i'', η)).
  Proof.
    intros Γ η θ i i' i'' d d' d'' p_fresh d_neq_0 r_i r_i' r_i''.
    intros [Δ s] t_Δ Γwf Δwf Γ_Δ.
    destruct p_fresh with (Γ:=(Γ ∪ Δ)) (η:=η) (s:=s) as [p].
    eapply antiex. constructor. apply H.
    assert (p_fresh_ΓΔηs:=H).
    destruct H. apply (fresh_for_heap_join Γ_Δ) in H.
    assert (as0 : add p (K (IfZ i' i''), η) (Γ ∪ Δ)
                          ≃
                  Γ ∪ add p (K (IfZ i' i''), η) (Γ ∪ Δ)
           ).
    - (* begin as0 *)
      symmetry.
      rewrite Join_comm_1. rewrite <- heap_add_prop_idemp'''. reflexivity.
      apply H. auto. auto. apply joinable_comm. apply Join_add_prop'. apply H.
      apply joinable_comm. apply joinable_join1. auto.
    (* end as0 *)
    assert (as1 : SetIn (Tests tint d)
                        (Map.add p (K (IfZ i' i''), η) (Γ ∪ Δ), ? p :: s)
           ).
    eapply tests_ifz. apply p_fresh_ΓΔηs.
    apply r_i'. apply r_i''. apply Γwf. auto. auto.
    destruct d. destruct d_neq_0. auto. simpl. auto. auto. auto.
    heap_rewrite_conf as0.
    specialize (r_i d (tset_refl (eta d)) _ as1).
    apply r_i. auto.
    split. apply wf_add. apply wf_union. auto. apply Γwf. apply Δwf.
    intros q q_in. apply join_in1. apply Γwf. auto.
    apply stack_ptr_cons_included_if.
    intros q q_in. apply F.add_in_iff. right. apply join_in2. apply Δwf. auto.
    apply F.add_in_iff. left. auto.
    apply joinable_comm. apply Join_add_prop'. apply H.
    apply joinable_comm. apply joinable_join1. auto.
  Qed.
  
  Lemma realizer_ifz :
    forall Γ η θ i i' i'' d d' d'',
      exists_fresh_pointer ->
      SetIn (Realizers tint (eta d)) (Γ, (i,η)) ->
      SetIn (Realizers θ d') (Γ, (i',η)) ->
      SetIn (Realizers θ d'') (Γ, (i'',η)) ->
      SetIn (Realizers θ (IfZSemInt d' d'' d)) (Γ, (iifz i i' i'', η)).
  Proof.
    intros Γ η θ i i' i'' d d' d'' p_fresh r_i r_i' r_i''.
    intros ifzv ifzv_eq_eta.
    destruct d.
    - (* dt =-= 0 *)
      simpl in ifzv_eq_eta.
      eapply tests_ifz_Z. auto.
      eapply realizers_Equal'. auto.
      apply r_i.
      eapply realizers_Equal'. apply ifzv_eq_eta.
      apply r_i'. apply r_i''.
    - (* dt > 0 *)
      simpl in ifzv_eq_eta.
      eapply tests_ifz_NZ. auto. instantiate (1:=(Z.pos p)).
      intro pos_neq_0. inversion pos_neq_0.
      apply r_i. apply r_i'.
      eapply realizers_Equal'. apply ifzv_eq_eta.
      apply r_i''.
    - (* dt < 0 *)
      simpl in ifzv_eq_eta.
      eapply tests_ifz_NZ. auto. instantiate (1:=(Z.neg p)).
      intro neg_neq_0. inversion neg_neq_0.
      apply r_i. apply r_i'.
      eapply realizers_Equal'. apply ifzv_eq_eta.
      apply r_i''.
  Qed.

  Lemma approx_rec_n : ∀ (c : ctx) (θ : type) (i : Code)
                         (d : ctx_denot (θ :: c) =-> ty_denot θ),
      exists_fresh_pointer ->
      @GRealizers (θ :: c) θ d i ->
      forall j, @GRealizers c θ (FChain _ _ j d) (irec i).
  Proof.
    intros c θ i d EFP IH j; fold ctx_denot.
    induction j.
    - Case "j = 0". apply g_bot_approx.
    - Case "j => j+1".
      intros Γ η ρ Hwf Her.
      specialize (IHj Γ η ρ).
      eapply realizers_Equal'. symmetry. rewrite <- FC_simpl. apply FC_Prop.
      intros dv dv_eq_eta. intros [Δ s] Δtest rwf twf Γ_Δ.
      destruct (EFP (Γ ∪ Δ) η s) as [p]. rename H into p_fresh.
      eapply antiex. constructor.  apply p_fresh.
      assert (Map.add p (C (irec i), η) (Γ ∪ Δ)
                      ≃
              Map.add p (C (irec i), η) Γ ∪ Δ).
      symmetry.
      eapply heap_add_prop''. destruct p_fresh. auto. auto.
      heap_rewrite_conf H. clear H.
      destruct p_fresh. apply fresh_for_heap_join in H.
      assert (extended_ρ : SetIn (EnvRealizers (θ :: c) (((FC d) j) ρ, ρ))
                                 (Map.add p (C (irec i), η) Γ, p :: η)).
      -- SCase "Assert extended env realizer".
         assert (Γ ∪ (⎨ p ⤇ (C (irec i), η) ⎬) ≃ Map.add p (C (irec i), η) Γ).
         --- SSCase "assert".
             rewrite <- (Join_add (Joinable_fresh (fst H))). reflexivity.
         eapply env_realizer_def. apply F.add_eq_o. auto.
         unfold HClos_to_MClos. simpl. reflexivity.
         eapply realizers_Equal. apply H1.
         apply realizer_extend_heap. auto. apply Joinable_fresh. apply (fst H).
         apply IHj. auto. auto.
         eapply env_realizers_Equal. apply H1.
         eapply env_realizer_extend_heap. apply rwf.
         apply Joinable_fresh. apply (fst H). auto.
      assert (extended_Γwf : heap_wf (Map.add p (C (irec i), η) Γ)).
      -- SCase "Assert extended heap well-formed".
         apply wf_add. apply rwf. apply rwf.
      specialize (IH (Map.add p (C (irec i), η) Γ) (p::η) (((FC d) j) ρ, ρ)
                     extended_Γwf extended_ρ dv dv_eq_eta (Δ,s) Δtest
                 ).
      apply IH. split. auto.
      eapply env_realizer_ptr. apply extended_ρ.
      auto.
      apply Join_add_prop'. apply H. auto. auto.
  Qed.
  
  Lemma clos_approx_rec_n:
    ∀ (θ1 : type) (c : ctx) (d : ctx_denot (θ1 :: c) =-> ty_denot θ1) (i : Code),
      exists_fresh_pointer ->
      @clos_Realizers (θ1 :: c) θ1 d i ->
      forall (n : nat), @clos_Realizers c θ1 (FChain _ _ n d) (irec i).
  Proof.
    intros θ1 c d i EFP IH n; fold ctx_denot in *.
    apply ic_cont_closed with (P:=flip (GRealizers (θ1 :: c) (a:=θ1)) i).
    intros p H. apply approx_rec_n; auto. auto.
  Qed.

  Lemma clos_approx_rec:
    ∀ (θ : type) (c : ctx) (d : ctx_denot (θ :: c) =-> ty_denot θ) (i : Code),
      exists_fresh_pointer ->
      @clos_Realizers (θ :: c) θ d i ->
      @clos_Realizers c θ (FixF d) (irec i).
  Proof.
    intros θ c d i EFP H; fold ctx_denot in *.
    have ic_closed := ideal_closure_closed
                       (flip (GRealizers c (a:=θ)) (irec i)).
    destruct ic_closed as [chain_c down_c]. eapply clos_realizers_Equal.
    rewrite <- FC_lub; auto. unfold SetIn, "∈" in *.
    apply chain_c. intros n.
    eapply clos_realizers_Equal.
    rewrite -> FC_simpl with (d:=d);fold ctx_denot; auto.
    have crn := @clos_approx_rec_n θ c d i EFP. apply crn.
    apply H.
  Qed.

  Lemma compiler_correctness_unit:
    ∀ (c : ctx) (d : ctx_denot c =-> t_ty_denot tunit),
      @GRealizers c tunit (eta << d) (ival iunit).
  Proof.
    intros c d Γ η ρ Hwf Her.
    eapply primitive_realizer.
    cbn. 
    eapply env_realizer_ptr ; eauto.
  Qed.

  Lemma clos_compiler_correctness_unit:
    ∀ (c : ctx) (d : ctx_denot c =-> t_ty_denot tunit),
      @clos_Realizers c tunit (eta << d) (ival iunit).
  Proof.
    intros c d.
    apply ideal_closure_sub.
    apply compiler_correctness_unit.
  Qed.

  Lemma compiler_correctness_int:
    ∀ (c : ctx) (z : Z),
      @GRealizers c tint (eta << const _ z) (ival (iint z)).
  Proof.
    intros c z Γ η ρ Hwf Her.
    eapply primitive_realizer.
    split. eapply env_realizer_ptr ; eauto. auto.
  Qed.

  Lemma clos_compiler_correctness_int:
    ∀ (c : ctx) (z : Z),
      @clos_Realizers c tint (eta << const _ z) (ival (iint z)).
  Proof.
    intros z c.
    apply ideal_closure_sub.
    apply compiler_correctness_int.
  Qed.
  
  Lemma compiler_correctness_var:
    ∀ (θ : type) (c : ctx) (v : var c θ),
      @GRealizers c θ (lookup v) (iaccess (var_to_nat v)).
  Proof.
    intros θ c v Γ η ρ Her.
    set (Q := nth_var_to_nat v).
    clearbody Q.
    rewrite (var_to_nat_lookup v ρ Q).
    eapply realizer_access ; auto.
  Qed.

  Lemma clos_compiler_correctness_var:
    ∀ (θ : type) (c : ctx) (v : var c θ),
      @clos_Realizers c θ (lookup v) (iaccess (var_to_nat v)).
  Proof.
    intros θ c v.
    apply ideal_closure_sub.
    apply compiler_correctness_var.
  Qed.
  
  Lemma compiler_correctness_abs:
    ∀ (θ1 θ2 : type) (c : ctx)
      (d : ctx_denot (θ1 :: c) =-> ty_denot θ2) (i : Code),
      @GRealizers (θ1 :: c) θ2 d i ->
      @GRealizers c (θ1 ⇾ θ2) (AbsTy d) (ival (igrab i)).
  Proof.
    intros θ1 θ2 c d i HI Γ η ρ Hwf Her.
    simpl. fold ctx_denot.
    eapply primitive_realizer.
    set (f := fun d' : ty_denot θ1 => d (d', ρ)).
    split.
    eapply env_realizer_ptr ; eauto.
    intros d' Γ' α β Hp0 Hwf1 Hjble β_to_α p Hjble1.
    set (Γ'' := Γ ∪ Γ' ∪ ⎨ p ⤇ β ⎬).
    assert ((Γ'', p :: η) ◈ ((d', ρ) : ctx_denot (θ1 :: c))) as He1.
    eapply env_realizer_realizer_cons. auto.
    apply HClos_prop'. apply β_to_α.
    auto. auto. auto. auto. auto.
    rewrite -> fold_Realizer in *.
    eapply HI.
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
  
  Lemma clos_compiler_correctness_abs:
    ∀ (θ1 θ2 : type) (c : ctx)
      (d : ctx_denot (θ1 :: c) =-> ty_denot θ2) (i : Code),
      @clos_Realizers (θ1 :: c) θ2 d i ->
      @clos_Realizers c (θ1 ⇾ θ2) (AbsTy d) (ival (igrab i)).
  Proof.
    intros θ1 θ2 c d i IH.
    intros A ss chain_c down_c.
    apply cont_closed with
        (f:=AbsTy)
        (P:=flip (GRealizers (θ1 :: c) (a:=θ2)) i).
    unfold closed. split. apply chain_c. apply down_c.
    intros p A_p.
    apply ss.
    apply compiler_correctness_abs. auto.
    apply IH.
  Qed.

  Lemma g_compiler_correctness_app:
    ∀ (θ1 θ2 : type) (c : ctx) (v : var c θ1) (i : Code)
      (d : ctx_denot c =-> ty_denot (θ1 ⇾ θ2)),
      @GRealizers c (θ1 ⇾ θ2) d i ->
      @GRealizers c θ2 (AppTy d (lookup v)) (ipush (var_to_nat v) i).
  Proof.
    intros θ1 θ2 c v i d IH.
    intros Γ η ρ Hwf Her.
    eapply realizers_Equal'. symmetry. rewrite sem_term_app_Eq. auto.
    set (Q := nth_var_to_nat v).
    clearbody Q.
    rewrite (var_to_nat_lookup v ρ Q).
    eapply realizer_push ; auto.
  Qed.

  Lemma clos_compiler_correctness_swap_app:
    ∀ (θ1 θ2 : type) (c : ctx) (v : var c θ1) (i : Code)
      (d : ctx_denot c =-> ty_denot (θ1 ⇾ θ2)),
      @clos_Realizers c (θ1 ⇾ θ2) d i ->
      @clos_Realizers c θ2 (SwapAppTy (lookup v) d) (ipush (var_to_nat v) i).
  Proof.
    intros θ1 θ2 c v i d IH.
    intros A ss chain_c down_c.
    apply cont_closed with
        (f:=SwapAppTy (lookup v))
        (P:=flip (GRealizers c (a:=θ1 ⇾ θ2)) i).
    unfold closed. split. apply chain_c. apply down_c.
    intros p A_p.
    apply ss. unfold flip in A_p. unfold flip.
    intros Γ η ρ H H0. eapply realizers_Equal'.
    rewrite <- AppTy_Prop. reflexivity.
    apply g_compiler_correctness_app;auto.
    auto.
  Qed.

  Lemma clos_compiler_correctness_app:
    ∀ (θ1 θ2 : type) (c : ctx) (v : var c θ1) (i : Code)
      (d : ctx_denot c =-> ty_denot (θ1 ⇾ θ2)),
      @clos_Realizers c (θ1 ⇾ θ2) d i ->
      @clos_Realizers c θ2 (AppTy d (lookup v)) (ipush (var_to_nat v) i).
  Proof.
    intros θ1 θ2 c v i d H.
    intros A ss chain_c down_c.
    eapply down_c. rewrite AppTy_Prop. reflexivity.
    apply (@clos_compiler_correctness_swap_app θ1 θ2 c v i d).
    auto. auto. auto. auto.
  Qed.

  Lemma clos_compiler_correctness_let:
    ∀ (θ1 θ2 : type) (c : ctx)
      (d : ctx_denot (θ1 :: c) =-> ty_denot θ1)
      (d' : ctx_denot (θ1 :: c) =-> ty_denot θ2)
      (i i' : Code),
      exists_fresh_pointer ->
      @clos_Realizers (θ1 :: c) θ1 d i ->
      @clos_Realizers (θ1 :: c) θ2 d' i' ->
      @clos_Realizers c θ2 (LetTy d' (FixF d)) (ilet (irec i) i').
  Proof.
    intros θ1 θ2 c d d' i i' EFP IH IH'; fold ctx_denot.
    apply ic_cont2_closed with
        (f:=LetTy)
        (P:=flip (GRealizers (θ1 :: c) (a:=θ2)) i')
        (Q:=flip (GRealizers c (a:=θ1)) (irec i)); fold ctx_denot.
    intros a b Ha Hb.
    intros Γ η ρ Γwf Her.
    intros dt2 dt2_eta.
    intros [Δ s] Δtest Γexwf Δwf Γ_Δ.
    destruct (EFP (Γ ∪ Δ) η s) as [p]. rename H into p_fresh.
    eapply antiex. constructor. apply p_fresh.
    destruct p_fresh. apply fresh_for_heap_join in H.
    -- assert (Γ ∪ (⎨ p ⤇ (C (irec i), η) ⎬)
                 ≃
               Map.add p (C (irec i), η) Γ).
       rewrite <- (Join_add (Joinable_fresh (fst H))). reflexivity.
    -- assert (extended_ρ : SetIn (EnvRealizers (θ1 :: c) (b ρ, ρ))
                                  (add p (C (irec i), η) Γ, p :: η)
              ).
       eapply env_realizer_def. apply F.add_eq_o. auto. reflexivity.
       unfold snd. eapply realizers_Equal. apply H1.
       apply realizer_extend_heap. auto. apply Joinable_fresh. apply (fst H).
       apply Hb. auto. auto.
       eapply env_realizers_Equal. apply H1.
       eapply env_realizer_extend_heap. auto.
       apply Joinable_fresh. apply (fst H). auto.
    -- assert (Map.add p (C (irec i), η) (Γ ∪ Δ)
                         ≃
                 Map.add p (C (irec i), η) Γ ∪ Δ).
       symmetry. eapply heap_add_prop''. apply fresh_for_heap_join_1.
       auto. auto. auto.
    heap_rewrite_conf H2. clear H2.
    -- assert (extended_Γwf : heap_wf (Map.add p (C (irec i), η) Γ)).
       apply wf_add. auto. apply Γexwf.
    specialize (Ha (Map.add p (C (irec i), η) Γ) (p :: η) (b ρ, ρ)
                       extended_Γwf extended_ρ).
    specialize (Ha dt2 dt2_eta (Δ,s) Δtest).
    apply Ha. split. auto. eapply env_realizer_ptr. apply extended_ρ. auto.
    apply Join_add_prop'. apply H. auto. auto.
    auto. apply clos_approx_rec; auto.
  Qed.
  
  Lemma g_compiler_correctness_bop:
    ∀ (bop : BOp) (c : ctx)
      (i i' : Code)
      (d d' : ctx_denot c =-> ty_denot tint),
      exists_fresh_pointer ->
      @GRealizers c tint d i ->
      @GRealizers c tint d' i' ->
      @GRealizers c tint (IntOpTy (semZBOp bop) d d') (ibop bop i i').
  Proof.
    intros b c i i' d d' EFP IH IH'.
    intros Γ η ρ Γwf Her.
    intros bopv bopv_eq. apply BOpTyValVal' in bopv_eq.
    inversion bopv_eq as [da [da' [? [? ?]]]].
    rewrite <- H1.
    apply tests_bop_3; fold term_denot; fold compile. auto.
    eapply realizers_Equal'. apply H. apply IH. auto. auto.
    eapply realizers_Equal'. apply H0. apply IH'. auto. auto.
  Qed.

  Lemma clos_compiler_correctness_bop:
    ∀ (bop : BOp) (c : ctx)
      (i i' : Code)
      (d d' : ctx_denot c =-> ty_denot tint),
      exists_fresh_pointer ->
      @clos_Realizers c tint d i ->
      @clos_Realizers c tint d' i' ->
      @clos_Realizers c tint (IntOpTy (semZBOp bop) d d') (ibop bop i i').
  Proof.
    intros b c i i' d d' EFP IH IH'.
    intros A ss chain_c down_c.
    apply cont2_closed with
        (f:=IntOpTy (semZBOp b))
        (P:=flip (GRealizers c (a:=tint)) i)
        (Q:=flip (GRealizers c (a:=tint)) i').
    unfold closed. split. apply chain_c. apply down_c.
    intros p q A_p A_q.
    apply ss. unfold flip in *.
    apply g_compiler_correctness_bop. auto. auto. auto.
    auto.
    auto.
  Qed.
  
  Lemma g_compiler_correctness_ifz:
    ∀ (θ : type) (c : ctx) (i i' i'' : Code)
      (d : ctx_denot c =-> ty_denot tint)
      (d' d'' : ctx_denot c =-> ty_denot θ),
      exists_fresh_pointer ->
      @GRealizers c tint d i ->
      @GRealizers c θ d' i' ->
      @GRealizers c θ d'' i'' ->
      @GRealizers c θ (IfZIntTy d d' d'') (iifz i i' i'').
  Proof.
    intros θ c i i' i'' d d' d'' EFP IH IH' IH''.
    intros Γ η ρ Γwf Her.
    intros ifzv ifzv_eq. apply IfZTyValVal' in ifzv_eq.
    destruct ifzv_eq as [dt [? ?]]. simpl in *.
    apply realizer_ifz with (d:=dt) (d':=d' ρ) (d'':=d'' ρ). auto.
    eapply realizers_Equal'. apply H.
    eapply IH; auto.
    apply IH'; auto.
    apply IH''; auto.
    rewrite <- H0. apply IfZSemInt_cont.
  Qed.

  Lemma clos_compiler_correctness_ifz:
    ∀ (θ : type) (c : ctx) (i i' i'' : Code)
      (d : ctx_denot c =-> ty_denot tint)
      (d' d'' : ctx_denot c =-> ty_denot θ),
      exists_fresh_pointer ->
      @clos_Realizers c tint d i ->
      @clos_Realizers c θ d' i' ->
      @clos_Realizers c θ d'' i'' ->
      @clos_Realizers c θ (IfZIntTy d d' d'') (iifz i i' i'').
  Proof.
    intros θ c i i' i'' d d' d'' EFP IH IH' IH''.
    intros A ss chain_c down_c.
    apply cont3_closed with
        (f:=IfZIntTy)
        (P:=flip (GRealizers c (a:=tint)) i)
        (Q:=flip (GRealizers c (a:=θ)) i')
        (R:=flip (GRealizers c (a:=θ)) i'').
    unfold closed. split. apply chain_c. apply down_c.
    intros p q r A_p A_q A_r.
    apply ss. unfold flip in *.
    apply g_compiler_correctness_ifz; auto. auto. auto. auto.
  Qed.
  
  Lemma g_compiler_correctness_pair:
    ∀ (θ1 θ2 : type) (c : ctx) (i i' : Code)
      (d : ctx_denot c =-> ty_denot θ1)
      (d' : ctx_denot c =-> ty_denot θ2),
      exists_fresh_pointer ->
      @GRealizers c θ1 d i ->
      @GRealizers c θ2 d' i' ->
      @GRealizers c (θ1 ⨱ θ2) (eta << prod_fun d d') (ival (ipair i i')).
  Proof.
    intros θ1 θ2 c i i' d d' EFP IH IH'.
    intros Γ η ρ Γwf Her.
    eapply primitive_realizer.
    split.
    eapply env_realizer_ptr; eauto.
    split.
    apply IH; auto.
    apply IH'; auto.
  Qed.

  Lemma clos_compiler_correctness_cprod_fun_pair:
    ∀ (θ1 θ2 : type) (c : ctx) (i i' : Code)
      (d : ctx_denot c =-> ty_denot θ1)
      (d' : ctx_denot c =-> ty_denot θ2),
      exists_fresh_pointer ->
      @clos_Realizers c θ1 d i ->
      @clos_Realizers c θ2 d' i' ->
      @clos_Realizers c (θ1 ⨱ θ2) (cprod_fun d d') (ival (ipair i i')).
  Proof.
    intros θ1 θ2 c i i' d d' EFP IH IH'.
    intros A ss chain_c down_c.
    apply cont2_closed with
        (f:=cprod_fun)
        (P:=flip (GRealizers c (a:=θ1)) i)
        (Q:=flip (GRealizers c (a:=θ2)) i').
    unfold closed. split. apply chain_c. apply down_c.
    intros p q A_p A_q.
    apply ss. unfold flip in *.
    intros Γ η ρ H H'. eapply realizers_Equal'. rewrite prod_fun_prop.
    reflexivity. apply g_compiler_correctness_pair; auto. auto. auto.
  Qed.

  Lemma clos_compiler_correctness_pair:
    ∀ (θ1 θ2 : type) (c : ctx) (i i' : Code)
      (d : ctx_denot c =-> ty_denot θ1)
      (d' : ctx_denot c =-> ty_denot θ2),
      exists_fresh_pointer ->
      @clos_Realizers c θ1 d i ->
      @clos_Realizers c θ2 d' i' ->
      @clos_Realizers c (θ1 ⨱ θ2) (eta << prod_fun d d') (ival (ipair i i')).
  Proof.
    intros θ1 θ2 c i i' d d' H H0 H1.
    intros A ss chain_c down_c.
    eapply down_c. setoid_rewrite <- prod_fun_prop. reflexivity.
    apply (@clos_compiler_correctness_cprod_fun_pair θ1 θ2 c i i' d d'); auto.
  Qed.

  Lemma g_compiler_correctness_fst:
    ∀ (θ1 θ2 : type) (c : ctx) (v : var c (θ1 ⨱ θ2)),
      @GRealizers c θ1 (kleisli (FST (ty_denot θ1) (ty_denot θ2)) << lookup v)
                       (ifst (var_to_nat v)).
  Proof.
    intros θ1 θ2 c v Γ η ρ Γwf Her.
    intros fstv fstv_eq_eta.
    simpl. apply FstTyValVal in fstv_eq_eta.
    destruct fstv_eq_eta as [d lookupVal].
    intros (Δ, s) Hp0 Hwf1 Hwf2 Hjble0.
    set (Q := nth_var_to_nat v); clearbody Q.
    set (H := env_realizer_lookup _ _ _ _ _ Q Her).
    clearbody H.
    destruct H  as [p [EQ EX]].
    destruct EX as [α [β [F1 [β_to_α Hr2]]]].
    eapply antiex.
    econstructor.
    apply EQ.
    eapply find_submap. apply join_sub1. auto. apply F1. apply β_to_α.
    eapply add_marker_pi1.
    eapply find_submap. apply join_sub1. auto. apply F1. apply β_to_α.
    rewrite <- var_to_nat_lookup in Hr2.
    assert (p_in_Γ : p ∈ heap_ptr Γ).
    unfold "∈", heap_ptr.
    apply Union_introl. eapply key_set_find_in.
    apply F1.
    eapply realizers_Equal' in Hr2. 2 : { apply lookupVal. }
    have TestsPair1 := tests_pairs_1 Hwf2 Hjble0
                     (tset_refl (T:= t_ty_denot θ1 _BOT * ty_denot θ2)
                                (eta fstv, d)) Hp0.
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
    specialize (TestsPair1 (Γ,α)).
    heap_rewrite_conf H.
    apply TestsPair1.
    apply Hr2. auto.
    eapply r_wf_find. auto. apply F1. apply β_to_α.
    split.
    apply wf_union. auto. auto.
    apply (t_wf_heap Hwf2).
    rewrite stack_ptr_eq_1.
    destruct Hwf2.
    rewrite (Join_key_set Hjble0).
    right. apply H1. auto.
    apply joinable_join1. auto.
  Qed.

  Lemma clos_compiler_correctness_fst:
    ∀ (θ1 θ2 : type) (c : ctx) (v : var c (θ1 ⨱ θ2)),
      @clos_Realizers c θ1
                      (kleisli (FST (ty_denot θ1) (ty_denot θ2)) << lookup v)
                      (ifst (var_to_nat v)).
  Proof.
    intros θ1 θ2 c v.
    apply ideal_closure_sub.
    apply g_compiler_correctness_fst.
  Qed.
  
  Lemma g_compiler_correctness_snd:
    ∀ (θ1 θ2 : type) (c : ctx) (v : var c (θ1 ⨱ θ2)),
      @GRealizers c θ2 (kleisli (SND (ty_denot θ1) (ty_denot θ2)) << lookup v)
                       (isnd (var_to_nat v)).
  Proof.
    intros θ1 θ2 c v Γ η ρ Γwf Her.
    intros sndv sndv_eq_eta.
    simpl. apply SndTyValVal in sndv_eq_eta.
    destruct sndv_eq_eta as [d lookupVal].
    intros (Δ, s) Hp0 Hwf1 Hwf2 Hjble0.
    set (Q := nth_var_to_nat v); clearbody Q.
    set (H := env_realizer_lookup _ _ _ _ _ Q Her).
    clearbody H.
    destruct H  as [p [EQ EX]].
    destruct EX as [α [β [F1 [β_to_α Hr2]]]].
    eapply antiex.
    econstructor.
    apply EQ.
    eapply find_submap. apply join_sub1. auto. apply F1. apply β_to_α.
    eapply add_marker_pi2.
    eapply find_submap. apply join_sub1. auto. apply F1. apply β_to_α.
    rewrite <- var_to_nat_lookup in Hr2.
    assert (p_in_Γ : p ∈ heap_ptr Γ).
    unfold "∈", heap_ptr.
    apply Union_introl. eapply key_set_find_in.
    apply F1.
    simpl in Hp0.
    simpl in *.
    eapply realizers_Equal' in Hr2. 2 : { apply lookupVal. }
    have TestsPair2 := tests_pairs_2 Hwf2 Hjble0
                        (tset_refl (T:= t_ty_denot θ1 _BOT * ty_denot θ2)
                                   (d, eta sndv)) Hp0.
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
    specialize (TestsPair2 (Γ,α)).
    heap_rewrite_conf H.
    apply TestsPair2.
    apply Hr2. auto.
    eapply r_wf_find. auto. apply F1. apply β_to_α.
    split.
    apply wf_union. auto. auto.
    apply (t_wf_heap Hwf2).
    rewrite stack_ptr_eq_2.
    destruct Hwf2.
    rewrite (Join_key_set Hjble0).
    right. apply H1. auto.
    apply joinable_join1. auto.
  Qed.

  Lemma clos_compiler_correctness_snd:
    ∀ (θ1 θ2 : type) (c : ctx) (v : var c (θ1 ⨱ θ2)),
      @clos_Realizers c θ2
                      (kleisli (SND (ty_denot θ1) (ty_denot θ2)) << lookup v)
                      (isnd (var_to_nat v)).
  Proof.
    intros θ1 θ2 c v.
    apply ideal_closure_sub.
    apply g_compiler_correctness_snd.
  Qed.
  
  (** Main theorem *)
  Theorem ideal_compiler_correctness :
    exists_fresh_pointer ->
    forall (π : ctx) (θ : type),
    forall (t : term π θ),
    @clos_Realizers π θ (⟦ t ⟧) (⦇ t ⦈).
  Proof.
    intro EFP.
    induction t0.
    - Case "term_unit".
      apply clos_compiler_correctness_unit.
    - Case "term_int".
      apply clos_compiler_correctness_int.
    - Case "term_var".
      apply clos_compiler_correctness_var.
    - Case "term_abs".
      apply clos_compiler_correctness_abs; fold term_denot compile; auto.
    - Case "term_app".
      apply clos_compiler_correctness_app; fold term_denot compile; auto.
    - Case "term_let".
      apply clos_compiler_correctness_let; fold term_denot compile; auto.
    - Case "term_bop".
      apply clos_compiler_correctness_bop; fold term_denot compile; auto.
    - Case "term_ifz".
      apply clos_compiler_correctness_ifz; fold term_denot compile; auto.
    - Case "term_pair".
      apply clos_compiler_correctness_pair; fold term_denot compile; auto.
    - Case "term_fst".
      apply clos_compiler_correctness_fst.
    - Case "term_snd".
      apply clos_compiler_correctness_snd.
  Qed.

End DenoApprox.

(* Local Variables: *)
(* company-coq-local-symbols: (("~>" . ?↣)) *)
(* End: *)
