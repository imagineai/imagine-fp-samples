Add Rec LoadPath "." as Top.
Set Implicit Arguments.

Require Import List.
Require Import Coq.Init.Datatypes.
Require Export Map.
Require Import Equalities.
Require Import Ensembles.
Require Import SetoidList.
Require Import Finite_sets.
Require Import Finite_sets_facts.
Require Import Coq.Program.Equality.
Require Import Sets.
Require Import ZArith.
Require Import BOp.

(** * Target Language. Machine transitions and components *)

Close Scope nat_scope.

Inductive Val : Type :=
| iunit : Val
| iint  : Z -> Val
| igrab : Code -> Val
| ipair : Code -> Code -> Val
(** Instructions *) 
with Code : Type :=
| ival    : Val  -> Code
| iaccess : nat   -> Code
| ipush   : nat   -> Code -> Code
| ilet    : Code -> Code -> Code
| ibop    : BOp  -> Code -> Code -> Code
| iifz    : Code -> Code -> Code -> Code
| ifst    : nat   -> Code
| isnd    : nat   -> Code
| irec    : Code -> Code
.

Module Machine (PointerType : UsualDecidableType).

  Definition Pointer := PointerType.t.

  Inductive Cont : Type :=
  | ZBOpL : Code -> Cont
  | ZBOpR : Val  -> Cont
  | IfZ   : Code -> Code -> Cont
  .

  Inductive HeapElem : Type :=
  | K : Cont -> HeapElem
  | C : Code -> HeapElem
  .
  
  Definition MEnv := list Pointer.
  Definition MClos : Type := Code * MEnv.
  Definition HClos : Type := HeapElem * MEnv.

  Module CodeTyp <: Equalities.Typ.
    Definition t := HeapElem.
  End CodeTyp.

  Module Export HeapM := UsualHeap PointerType CodeTyp.

  Definition HClos_to_MClos (he : HClos) : option MClos :=
    match fst he with
    | K _ => None
    | C c => Some (c, snd he)
    end.

  Definition MClos_to_HClos (α : MClos) : HClos := (C (fst α), snd α).

  Lemma HClos_prop : forall α β,
      HClos_to_MClos β = Some α -> MClos_to_HClos α = β.
  Proof.
    intros α β H.
    unfold MClos_to_HClos. destruct β. destruct h.
    inversion H. inversion H. auto.
  Qed.

  Lemma HClos_prop' : forall α β,
      MClos_to_HClos α = β -> HClos_to_MClos β = Some α.
  Proof.
    intros α β H.
    unfold MClos_to_HClos in H. rewrite <- H. destruct α.
    auto.
  Qed.
  
  (** Range of a heap *)
  Definition heap_range_ptr (Γ : Heap) : KeySet
      := fun k => exists k', exists i, exists η,  Map.MapsTo k' (i, η) Γ /\ List.In k η.

  (** Pointers occurring in the heap, (domain and range) *)
  Definition heap_ptr (Γ : Heap) : KeySet := Union _ (key_set Γ)
                                                    (heap_range_ptr Γ).

  (** A heap is well formed if all its pointers occur in its domain *)
  Definition heap_wf Γ : Prop := Same_set _ (heap_ptr Γ) (key_set Γ).    

  (** Stacks hold "markers" to signal an application or an update of a pointer *)
  Inductive Marker : Type :=
  | mapply     : Pointer -> Marker
  | mupdate    : Pointer -> Marker
  | mapplypi1  : Marker
  | mapplypi2  : Marker
  | mupdatepi1 : Pointer -> Marker
  | mupdatepi2 : Pointer -> Marker
  | bopapply   : Pointer -> BOp -> Marker
  | ifzapply   : Pointer -> Marker
  .
  
  Notation "⌑ p" := (mapply p) (at level 10).
  Notation "# p" := (mupdate p) (at level 10).
  (* Definition π1 := mapplypi1. *)
  (* Definition π2 := mapplypi1. *)
  Notation "#1 p" := (mupdatepi1 p) (at level 10).
  Notation "#2 p" := (mupdatepi2 p) (at level 10).
  Notation "⦿ p bop" := (bopapply p bop) (at level 10).
  Notation "? p" := (ifzapply p) (at level 10).
  
  Definition stack := list Marker.

  (** The pointer behind the marker *)
  (* Definition maker_pointer (δ : Marker) : Pointer := *)
  (*   match δ with *)
  (*   | ⌑ p => p *)
  (*   | # p => p *)
  (*   end. *)
  
  Definition conf := Heap * MClos * stack.

  Implicit Type s  : stack.
  Implicit Type η  : MEnv.
  Implicit Type p  : Pointer.
  Implicit Type i  : Code.
  Implicit Type he : HeapElem.
  Implicit Type Γ  : Heap.
  Implicit Type n  : nat.
  Implicit Type α  : MClos.
  Implicit Type β  : HClos.
  Implicit Type w  : conf.

  (** Set of pointers of an environment **)
  Definition env_ptr η : KeySet := fun p => List.In p η.

  (** Set of pointers of an stack *)
  Definition stack_ptr s : KeySet :=
    fun p => List.In (⌑ p) s \/
           List.In (# p) s \/
           List.In (mupdatepi1 p) s \/
           List.In (mupdatepi2 p) s \/
           (exists bop, List.In (bopapply p bop) s) \/
           List.In (ifzapply p) s.

  (** A configuration if well formed if all the pointers in the environment and
the stack belong to the domain of the heap, and also the heap itself is
wellformed *)
  
  Definition conf_wf (conf : conf) :=
    match conf with
      (Γ, (i, η), s) => heap_wf Γ /\
                          Included _ (env_ptr η) (key_set Γ) /\
                          Included _ (stack_ptr s) (key_set Γ)
    end.

  (** Notion of pointer freshness *)
  Definition fresh_for_heap  p Γ := ~ SetIn (heap_ptr Γ) p.
  Definition fresh_for_env p η := ~ SetIn (env_ptr η) p.
  Definition fresh_for_stack p s :=  ~ SetIn (stack_ptr s) p.
  Definition fresh_for p Γ η s := fresh_for_heap p Γ /\
                                 fresh_for_stack p s /\ fresh_for_env p η.

  Reserved Notation "w ↦ y" (at level 70, no associativity).

  (** Transition rules of the machine *)
  Inductive trans : conf -> conf -> Prop :=
  (** Update *)
  | ival_update : forall Γ η p s iv,
      (Γ, (ival iv,η), # p :: s) ↦ (Map.add p (C (ival iv),η) Γ, (ival iv,η), s)
  | ival_update_1 : forall Γ i i' η η' p s iv,
      Map.find p Γ = Some ((C (ival (ipair i i')), η')) ->
      let α := (C (ival (ipair (ival iv) i')), η') in
      (Γ, (ival iv, η), mupdatepi1 p :: s) ↦ (Map.add p α Γ, (ival iv, η), s)
  | ival_update_2 : forall Γ i i' η η' p s iv,
      Map.find p Γ = Some (C (ival (ipair i i')), η') ->
      let α := (C (ival (ipair i (ival iv))), η') in
      (Γ, (ival iv, η), mupdatepi2 p :: s) ↦ (Map.add p α Γ, (ival iv, η), s)
  (** Apply Grab *)
  | tgrab_apply : forall Γ i η  p s,
      (Γ, (ival (igrab i), η), ⌑ p :: s) ↦ (Γ, (i, p :: η) , s)
  (** Ifz 0 *)
  | tifz_0 : forall Γ η η' i' i'' p s,
      Map.find p Γ = Some (K (IfZ i' i''), η') ->
      (Γ, (ival (iint 0%Z),η), ? p :: s)
        ↦
      (Γ, (i',η'), s)
  (** Ifz z ≠ 0 *)
  | tifz_n0 : forall Γ η η' i' i'' p s z,
      Map.find p Γ = Some (K (IfZ i' i''), η') ->
      z <> 0%Z ->
      (Γ, (ival (iint z%Z),η), ? p :: s)
        ↦
      (Γ, (i'',η'), s)  
  (** Access *)                           
  | taccess : forall Γ η p s n α β,
      nth_error η n = Some p ->
      Map.find p Γ = Some β ->
      HClos_to_MClos β = Some α ->
      (Γ, (iaccess n, η), s) ↦ (Γ, α, # p :: s)
  (** Push *)
  | tpush : forall Γ η p s n i,
      nth_error η n = Some p ->
      (Γ, (ipush n i, η), s) ↦ (Γ, (i, η), ⌑ p :: s)
  (** Let *)
  | tlet : forall Γ i i' η p s,
      fresh_for p Γ η s ->
      (Γ, (ilet i i', η), s) ↦ (Map.add p (C i, η) Γ, (i', p :: η), s)
  (** Apply π1 *)
  | tpair_apply_pi1 : forall Γ η i i' s,
      (Γ, (ival (ipair i i'), η), mapplypi1 :: s) ↦ (Γ, (i,η), s)
  (** Apply π2 *)
  | tpair_apply_pi2 : forall Γ η i i' s,
      (Γ, (ival (ipair i i'), η), mapplypi2 :: s) ↦ (Γ, (i',η), s)
  (** Ifz *)
  | tifz : forall Γ η i i' i'' p s,
      fresh_for p Γ η s ->
      (Γ, (iifz i i' i'', η), s)
        ↦
      (Map.add p (K (IfZ i' i''), η) Γ, (i,η), ? p :: s)
  (** Fst *)
  | tfst : forall Γ n η p s α β,
      nth_error η n = Some p ->
      Map.find p Γ = Some β ->
      HClos_to_MClos β = Some α ->
      (Γ, (ifst n, η), s)
        ↦
      (Γ, α, # p :: (mapplypi1 :: (#1 p :: s)))
  (** Snd *)
  | tsnd : forall Γ n η p s α β,
      nth_error η n = Some p ->
      Map.find p Γ = Some β ->
      HClos_to_MClos β = Some α ->
      (Γ, (isnd n, η), s)
        ↦
      (Γ, α, # p :: (mapplypi2 :: (#2 p :: s)))
  (** BOp Apply 1 *)
  | tbop_apply_1 : forall bop Γ i i' η p s,
      fresh_for p Γ η s ->
      (Γ, (ibop bop i i', η), s)
        ↦
      (Map.add p (K (ZBOpL i'), η) Γ, (i, η), bopapply p bop :: s)
  (** BOp Apply 2 *)
  | tbop_apply_2 : forall bop Γ z i' η η' p s,
      Map.find p Γ = Some (K (ZBOpL i'), η) ->
      (Γ, (ival (iint z), η'), bopapply p bop :: s)
        ↦
      (Map.add p (K (ZBOpR (iint z)), η') Γ, (i', η), bopapply p bop :: s)
  (** BOp Apply 3 *)
  | tbop_apply_3 : forall bop Γ z z' η η' p s,
      Map.find p Γ = Some (K (ZBOpR (iint z)), η) ->
      let iv := ival (iint (semZBOp bop z z')) in
      (Γ, (ival (iint z'), η'), bopapply p bop :: s)
        ↦
      (Γ, (iv, η), s)
  (** Rec Eval *)
  | rec_eval : forall Γ i η p s,
      fresh_for p Γ η s ->
      (Γ, (irec i, η), s)
        ↦
      (Map.add p (C (irec i), η) Γ, (i, p::η), s)
  where "w1 ↦ w2" := (trans w1 w2).

  (** Equality of configurations *)
  Definition conf_eq (w w' : conf) :=
    match w, w' with
      (Γ, α, s), (Γ', α', s') => Γ ≃ Γ' /\  α = α' /\ s = s'
    end.

  Notation "w [==] w'" := (conf_eq w w') (at level 70, no associativity).
    
  Lemma env_ptr_cons_included:
    forall p η X, Included _ (env_ptr η) X -> SetIn X p ->
             Included _ (env_ptr (p :: η)) X .
  Proof.
    intros p η X In1 In2.
    intros q In3.
    cbn in In3.
    destruct In3 as [EQ | In4].
    subst.
    auto.
    eapply In1.
    auto.
  Qed.

  Lemma stack_ptr_cons_included:
    forall p s X, Included _ (stack_ptr s) X ->
             SetIn X p ->
             Included _ (stack_ptr (⌑ p :: s)) X .
  Proof.
    intros p η X In1 In2.
    intros q In3.
    unfold Ensembles.In in In3.
    unfold stack_ptr in In3.
    destruct In3 as [H | H'].
    set (E := List.in_inv H).
    destruct E as [E1 | E2].
    injection E1. intros. subst.
    auto.
    eapply In1.
    left. auto. inversion H'.
    set (E := List.in_inv H).
    destruct E as [E1 | E2].
    discriminate.
    eapply In1.
    right. auto.
    inversion H.
    set (E := List.in_inv H0).
    destruct E as [E1 | E2].
    discriminate.
    eapply In1.
    right. auto.
    inversion H0.
    set (E := List.in_inv H1).
    destruct E as [E1 | E2].
    discriminate.
    eapply In1. right. auto.
    inversion H1.
    eapply In1. do 4 right. left.
    destruct H2 as [bop].
    set (E := List.in_inv H2).
    destruct E as [E1 | E2].
    discriminate. exists bop. auto.
    inversion H2.
    discriminate. 
    eapply In1. do 5 right. auto.
  Qed.

  Lemma stack_ptr_cons_included2:
    forall p s X, Included _ (stack_ptr s) X ->
             SetIn X p ->
             Included _ (stack_ptr (mupdatepi1 p :: s)) X.
  Proof.
    intros p η X In1 In2.
    intros q In3.
    unfold Ensembles.In in In3.
    unfold stack_ptr in In3.
    destruct In3 as [H | H'].
    set (E := List.in_inv H).
    destruct E as [E1 | E2].
    discriminate.
    eapply In1. left. auto.
    destruct H' as [H | H''].
    set (E := List.in_inv H).
    destruct E as [E1 | E2].
    discriminate.
    eapply In1. right. auto.
    destruct H'' as [H | H'].
    set (E := List.in_inv H).
    destruct E as [E1 | E2].
    injection E1. intros. subst.
    auto.
    eapply In1.
    right. right. left. auto.
    destruct H' as [H | H''].
    set (E := List.in_inv H).
    destruct E as [E1 | E2].
    discriminate.
    eapply In1. right. auto.
    eapply In1. do 4 right.
    destruct H'' as [H | H'].
    destruct H as [bop].
    set (E := List.in_inv H).
    destruct E as [E1 | E2].
    discriminate. left. exists bop. auto.
    inversion H'.
    discriminate. right. auto.
  Qed.

  Lemma stack_ptr_cons_included_bop :
    forall bop p s X, Included _ (stack_ptr s) X ->
             SetIn X p ->
             Included _ (stack_ptr (bopapply p bop :: s)) X.
  Proof.
    intros bop p η X In1 In2.
    intros q In3.
    unfold Ensembles.In in In3.
    unfold stack_ptr in In3.
    destruct In3 as [H | H'].
    set (E := List.in_inv H).
    destruct E as [E1 | E2]. discriminate.
    eapply In1. left. auto.
    inversion H'.
    set (E := List.in_inv H).
    destruct E as [E1 | E2].
    discriminate.
    eapply In1.
    right. auto.
    inversion H.
    set (E := List.in_inv H0).
    destruct E as [E1 | E2].
    discriminate.
    eapply In1.
    right. auto.
    inversion H0.
    set (E := List.in_inv H1).
    destruct E as [E1 | E2].
    discriminate.
    eapply In1.
    right. auto.
    inversion H1.
    destruct H2 as [bop'].
    inversion H2.
    injection H3. intros H4 H5. subst.
    auto.
    eapply In1. do 4 right. left.
    exists bop'. auto.
    inversion H2.
    discriminate.
    eapply In1. do 5 right. auto.
  Qed.

  Lemma stack_ptr_cons_included_if:
    forall p s X, Included _ (stack_ptr s) X ->
             SetIn X p ->
             Included _ (stack_ptr (? p :: s)) X .
  Proof.
    intros p η X In1 In2.
    intros q In3.
    unfold Ensembles.In in In3.
    unfold stack_ptr in In3.
    destruct In3 as [H | H'].
    set (E := List.in_inv H).
    destruct E as [E1 | E2].
    discriminate.
    eapply In1.
    left. auto. inversion H'.
    set (E := List.in_inv H).
    destruct E as [E1 | E2].
    discriminate.
    eapply In1.
    right. auto.
    inversion H.
    set (E := List.in_inv H0).
    destruct E as [E1 | E2].
    discriminate.
    eapply In1.
    right. auto.
    inversion H0.
    set (E := List.in_inv H1).
    destruct E as [E1 | E2].
    discriminate.
    eapply In1. right. auto.
    inversion H1.
    eapply In1. do 4 right. left.
    destruct H2 as [bop].
    set (E := List.in_inv H2).
    destruct E as [E1 | E2].
    discriminate. exists bop. auto.
    set (E := List.in_inv H2).
    destruct E as [E1 | E2].
    injection E1. intros. subst. auto.
    eapply In1. do 5 right. auto.
  Qed.
  
  Lemma stack_ptr_eq_1:
    forall s, Same_set PointerType.t (stack_ptr (mapplypi1 :: s)) (stack_ptr s).
  Proof.
    intro s.
    apply Same_set_in_iff.
    intro p.
    split.
    - (* ⇒ *)
      intro H.
      inversion H.
      destruct H0 as [E1 | E2].
      discriminate.
      left. auto.
      inversion H0.
      destruct H1 as [E1 | E2].
      discriminate.
      right. left. auto.
      inversion H1.
      destruct H2 as [E1 | E2].
      discriminate.
      right. right. left. auto.
      inversion H2.
      destruct H3 as [E1 | E2].
      discriminate.
      right. right. right. auto.
      inversion H3. inversion H4. inversion H5.
      discriminate.
      do 4 right. left. exists x. auto.
      inversion H4.
      discriminate.
      do 5 right. auto.
    - (* ⇐ *)
      intro H.
      destruct H as [H0 | [H1 | [H2 | [H3 | [H4 | H5]]]]].
      left. apply in_cons. auto.
      right. left. apply in_cons. auto.
      right. right. left. apply in_cons. auto.
      right. right. right. left. apply in_cons. auto.
      right. right. right. right. left. destruct H4. exists x. apply in_cons. auto.
      right. right. right. right. right. apply in_cons. auto.
  Qed.

  Lemma stack_ptr_eq_2:
    forall s, Same_set PointerType.t (stack_ptr (mapplypi2 :: s)) (stack_ptr s).
  Proof.
    intro s.
    apply Same_set_in_iff.
    intro p.
    split.
    - (* ⇒ *)
      intro H.
      inversion H.
      destruct H0 as [E1 | E2].
      discriminate.
      left. auto.
      inversion H0.
      destruct H1 as [E1 | E2].
      discriminate.
      right. left. auto.
      inversion H1.
      destruct H2 as [E1 | E2].
      discriminate.
      right. right. left. auto.
      inversion H2.
      destruct H3 as [E1 | E2].
      discriminate.
      right. right. right. auto.
      inversion H3. inversion H4. inversion H5.
      discriminate.
      do 4 right. left. exists x. auto.
      inversion H4.
      discriminate.
      do 5 right. auto.
    - (* ⇐ *)
      intro H.
      destruct H as [H0 | [H1 | [H2 | [H3 | [H4 | H5]]]]].
      left. apply in_cons. auto.
      right. left. apply in_cons. auto.
      right. right. left. apply in_cons. auto.
      right. right. right. left. apply in_cons. auto.
      right. right. right. right. left. destruct H4. exists x. apply in_cons. auto.
      right. right. right. right. right. apply in_cons. auto.
  Qed.
  
  Lemma Join_range_ptr:
    forall Γ Δ, Γ ⋈ Δ  ->
           Same_set _ (heap_range_ptr (Γ ∪ Δ))
                      (Union _ (heap_range_ptr Γ) (heap_range_ptr Δ)).
  Proof.
    intros Γ Δ Hjble.
    split.
    intros p In1.
    destruct In1 as [q [i [η [M1 In2]]]].
    destruct_MapsTo_join H1 H2.
    eapply Union_introl.
    exists q. exists i. exists η.
    auto.
    eapply Union_intror.
    exists q. exists i. exists η.
    auto.
    intros p In1.
    assert (Union _ (heap_range_ptr Γ) (heap_range_ptr Δ) p) as In1'.
    auto.                                   
    destruct In1' as [q In2 | q In3].
    destruct In2 as [q' [i [η [M1 In2]]]].
    exists q'. exists i. exists η.
    split.
    eapply MapRaw.MapsTo_join_1 ; auto.
    auto.
    destruct In3 as [q' [i [η [M1 In2]]]].
    exists q'. exists i. exists η.
    split.
    eapply Submap_MapsTo_leibniz ; auto.
    eapply join_sub2 ; auto.
    auto. auto.
  Qed.

  Lemma Join_heap_ptr:
    forall Γ Δ, Γ ⋈ Δ  ->
           Same_set _ (heap_ptr (Γ ∪ Δ)) (Union _ (heap_ptr Γ) (heap_ptr Δ)).
  Proof.
    intros Γ Δ Hjble.
    unfold heap_ptr.
    rewrite Join_range_ptr.
    rewrite Join_key_set.
    rewrite Same_set_in_iff.
    intro k.
    repeat rewrite Union_in_iff.
    tauto.
    auto.
    auto.
  Qed.
        
  Lemma wf_union: forall  Γ Δ : Heap, Γ ⋈ Δ -> heap_wf Γ -> heap_wf Δ -> heap_wf (Γ ∪ Δ).
    intros Γ Δ Hjble Hwf0 Hwf1.
    unfold heap_wf in *.
    rewrite Join_key_set.
    rewrite Join_heap_ptr.
    rewrite Hwf0.
    rewrite Hwf1.
    rewrite Same_set_in_iff.
    intro k.
    repeat rewrite Union_in_iff.
    tauto.
    auto.
    auto.
  Qed.

  Lemma find_heap_range:
    forall η Γ p he,
      find p Γ = Some (he, η) ->
      Included _ (env_ptr η) (heap_range_ptr Γ).
  Proof.
    intros η Γ p he Hf.
    intros q I.
    unfold env_ptr in I.
    unfold Ensembles.In in I.
    exists p. exists he. exists η.
    split.
    rewrite F.find_mapsto_iff ;
      auto.
    auto.
  Qed.

  Lemma heap_range_singleton:
    forall Γ he η p,
      Same_set _ (heap_range_ptr (⎨ p ⤇ (he, η) ⎬)) (env_ptr η).
  Proof.
    intros Γ he η p.
    split.
    intros q I.
    destruct I as [q' [i' [η' [EQ I']]]].
    unfold singleton in EQ.
    rewrite F.add_mapsto_iff in EQ.
    destruct EQ as [[EQ1 EQ2] | H'].
    injection EQ2. intros. subst.
    auto.
    destruct H' as [_ H'].
    rewrite F.empty_mapsto_iff in H'.
    contradiction.
    intros q I.
    exists p. exists he. exists η.
    split.
    eapply MapsTo_singleton.
    auto.
  Qed.

  Lemma heap_range_Included:
    forall Γ Δ, Γ ≃ Δ -> Included _ (heap_range_ptr Γ) (heap_range_ptr Δ).
  Proof.
    intros Γ Δ EQ.
    intros p I.
    destruct I as [q [i [η [Hf I']]]].
    exists q. exists i. exists  η.
    split.
    rewrite <- EQ.
    auto.
    auto.
  Qed.

  Lemma heap_range_Same:
    forall Γ Δ, Γ ≃ Δ -> Same_set _ (heap_range_ptr Γ) (heap_range_ptr Δ).
  Proof.
    intros Γ Δ EQ.
    split ;
    eapply heap_range_Included ;
    auto.
    symmetry.
    auto.
  Qed.

  Add Parametric Morphism : (heap_range_ptr) with
      signature Equal ==> (Same_set PointerType.t)
        as heap_range_ptr_mor.
  Proof.
    eapply heap_range_Same.
  Qed.

  Lemma heap_ptr_Included:
    forall Γ Δ, Γ ≃ Δ -> Included _ (heap_ptr Γ) (heap_ptr Δ).
  Proof.
    intros Γ Δ EQ.
    unfold heap_ptr.
    rewrite Equal_key_set.
    2 : { eauto. }
    rewrite EQ.
    auto with sets.
  Qed.

  Lemma heap_ptr_Same:
    forall Γ Δ, Γ ≃ Δ -> Same_set _ (heap_ptr Γ) (heap_ptr Δ).
  Proof.
    intros Γ Δ EQ.
    split ;
      eapply heap_ptr_Included ;
      auto.
    symmetry.
    auto.
  Qed.

  Add Parametric Morphism : (heap_ptr) with
      signature Equal ==> (Same_set PointerType.t)
        as heap_ptr_mor.
  Proof.
    eapply heap_ptr_Same.
  Qed.

  Add Parametric Morphism : (key_set) with
      signature Equal ==> (Same_set PointerType.t)
        as key_set_mor.
  Proof.
    eapply Equal_key_set.
  Qed.

  Add Parametric Morphism : (heap_wf) with
      signature Equal ==> impl
        as heap_wf_impl_mor.
  Proof.
    intros Γ Δ EQ.
    intro Hwf.
    unfold heap_wf in *.
    transitivity (heap_ptr Γ).
    rewrite EQ. reflexivity.
    transitivity (key_set Γ).
    auto.
    rewrite EQ. reflexivity.
  Qed.

  Lemma key_set_singleton:
    forall Γ he η p,
      Same_set _ (key_set (⎨ p ⤇ (he, η) ⎬)) (Singleton _ p).
  Proof.
    intros Γ i η p.
    split.
    intros q I.
    unfold Ensembles.In in I.
    unfold key_set in I.
    unfold singleton in I.
    rewrite F.add_in_iff in I.
    destruct I as [H1 | H2].
    rewrite H1.
    constructor.
    rewrite F.empty_in_iff in H2.
    contradiction.
    intros q I.
    destruct I.
    exists (i, η).
    eapply MapsTo_singleton.
  Qed.

  Lemma Joinable_fresh:
    forall Γ p β, fresh_for_heap p Γ ->
             Γ ⋈ ⎨ p ⤇ β ⎬.
  Proof.
    intros Γ p β fresh.
    unfold fresh_for_heap in fresh.
    unfold heap_ptr in fresh.
    assert (~ Map.SetIn (key_set Γ) p).
    intro M.
    eapply fresh.
    constructor. auto.
    unfold key_set in H.
    eapply Joinable_not_in.
    auto.
  Qed.

  Lemma Join_add_prop' : forall Γ Δ p β,
    fresh_for_heap p Δ ->
    Γ ⋈ Δ ->
    add p β Γ ⋈ Δ.
  Proof.
    intros Γ Δ p β p_fresh_Δ Γ_Δ.
    apply Joinable_fresh with (β:=β) in p_fresh_Δ.
    apply Join_add_prop. auto. auto.
  Qed.

    Lemma heap_add_prop' : forall Γ Δ p β,
      fresh_for_heap p Δ ->
      Γ ⋈ Δ ∪ (⎨ p ⤇ β ⎬) ->
      (Γ ∪ add p β Δ) ≃ add p β (Γ ∪ Δ).
  Proof.
    intros Γ Δ p β p_fresh_Δ Hjble.
    apply heap_add_prop.
    apply Joinable_fresh. auto.
    auto.
  Qed.

  Lemma heap_add_prop_idemp'' : forall Γ Δ p β,
      fresh_for_heap p Δ ->
      Γ ⋈ Δ ->
      add p β (Γ ∪ Δ) ≃ (add p β (Γ ∪ Δ)) ∪ Δ.
  Proof.
    intros Γ Δ p β p_fresh_Δ Γ_Δ.
    apply Joinable_fresh with (β:=β) in p_fresh_Δ.
    apply heap_add_prop_idemp. auto. auto.
  Qed.

  Lemma heap_add_prop_idemp''' : forall Γ Δ p β,
      fresh_for_heap p Γ ->
      Γ ⋈ Δ ->
      add p β (Γ ∪ Δ) ≃ (add p β (Γ ∪ Δ)) ∪ Γ.
  Proof.
    intros Γ Δ p β p_fresh_Γ Γ_Δ.
    apply Joinable_fresh with (β:=β) in p_fresh_Γ.
    apply heap_add_prop_idemp'. auto. auto.
  Qed.
  
  Lemma fresh_for_heap_join : forall Γ Δ p,
      Γ ⋈ Δ ->
      fresh_for_heap p (Γ ∪ Δ) ->
      fresh_for_heap p (Γ) /\ fresh_for_heap p (Δ).
  Proof.
    intros Γ Δ Γ_join_Δ p p_fresh_ΓΔ.
    split. intro p_in. destruct p_in.
    apply Union_introl with (C:=key_set Δ) in H.
    apply Join_key_set in H.
    apply Union_introl with (C:=heap_range_ptr (Γ ∪ Δ)) in H.
    apply p_fresh_ΓΔ in H. inversion H. auto.
    apply Union_introl with (C:=heap_range_ptr Δ) in H.
    apply Join_range_ptr in H.
    apply Union_intror with (B:=key_set (Γ ∪ Δ)) in H.
    apply p_fresh_ΓΔ in H. inversion H. auto.
    intro p_in. destruct p_in.
    apply Union_intror with (B:=key_set Γ) in H.
    apply Join_key_set in H.
    apply Union_introl with (C:=heap_range_ptr (Γ ∪ Δ)) in H.
    apply p_fresh_ΓΔ in H. inversion H. auto.
    apply Union_intror with (B:=heap_range_ptr Γ) in H.
    apply Join_range_ptr in H.
    apply Union_intror with (B:=key_set (Γ ∪ Δ)) in H.
    apply p_fresh_ΓΔ in H. inversion H. auto.
  Qed.

  Lemma fresh_for_heap_join_1 : forall Γ Δ p,
      Γ ⋈ Δ ->
      fresh_for_heap p (Γ) /\ fresh_for_heap p (Δ) ->
      fresh_for_heap p (Γ ∪ Δ).
  Proof.
    intros Γ Δ Γ_join_Δ p [p_fresh_Γ p_fresh_Δ].
    intro p_in. destruct p_in.
    apply Join_key_set in H.
    destruct H.
    apply Union_introl with (C:=heap_range_ptr Γ) in H.
    apply p_fresh_Γ in H. inversion H.
    apply Union_introl with (C:=heap_range_ptr Δ) in H.
    apply p_fresh_Δ in H. inversion H. auto.
    destruct H as [k [i [η [? ?]]]].
    apply join_MapsTo in H.
    destruct H.
    apply p_fresh_Γ.
    apply Union_intror.
    exists k, i, η. auto.
    apply p_fresh_Δ.
    apply Union_intror.
    exists k, i, η. auto.
  Qed.

  Lemma heap_add_join_prop : forall Γ Δ p β,
      fresh_for_heap p Γ ->
      Γ ⋈ Δ ->
      (add p β Γ) ∪ (add p β Δ) ≃ Γ ∪ (add p β Δ).
  Proof.
    intros Γ Δ p β p_fresh Γ_Δ.
    apply Joinable_Equal_1.
    split. intros H.
    apply join_in in H. destruct H.
    apply F.add_in_iff in H. destruct H.
    apply join_in2. apply F.add_in_iff.
    left. auto.
    apply join_in1. auto.
    apply join_in2. auto.
    intros H.
    apply join_in in H. destruct H.
    apply join_in1.
    apply F.add_in_iff.
    right. auto.
    apply join_in2. auto.
    apply Joinable_join_intro_r.
    apply Joinable_join_intro_l.
    apply Join_add_prop'. auto. apply Joinable_refl.
    apply Join_add_prop'. auto. auto.
    apply Joinable_join_intro_l.
    apply Join_add_prop''. auto.
    apply Join_add_prop''. apply Joinable_refl.
  Qed.

  Lemma Join_fresh_add_prop : forall Γ Δ p β,
      fresh_for_heap p Δ ->
      Γ ⋈ Map.add p β Δ ->
      Γ ⋈ Δ.
  Proof.
    intros Γ Δ p β p_fresh Γ_pΔ.
    intro k. intros e e' H H0.
    apply Γ_pΔ with (k:=k). auto.
    apply F.add_mapsto_iff. right.
    split. intros p_k. rewrite <- p_k in *.
    apply p_fresh.
    unfold heap_ptr.
    apply Union_introl. 
    apply key_set_find_in with(e:=e').
    apply find_1. auto. auto.
  Qed.

  Lemma heap_add_prop'' : forall Γ Δ p β,
      fresh_for_heap p (Γ ∪ Δ) ->
      Γ ⋈ Δ ->
      (add p β Γ ∪ Δ) ≃ add p β (Γ ∪ Δ).
  Proof.
    intros Γ Δ p β p_fresh Hjble.
    apply fresh_for_heap_join in p_fresh.
    rewrite Join_comm_1. rewrite heap_add_prop.
    apply F.add_m. auto. auto. auto.
    apply Joinable_fresh.
    apply p_fresh. auto.
    apply Joinable_join_intro_r. auto.
    apply Joinable_fresh.
    apply p_fresh. auto.
    apply Join_add_prop'.
    apply p_fresh. auto.
    auto.
  Qed.

  Lemma heaps_prop_ifz : forall Γ Γ' Δ p β,
      fresh_for_heap p (Γ ∪ Δ) ->
      Γ ⋈ Δ ->
      Γ' ⋈ Map.add p β (Γ ∪ Δ) ->
      Γ' ∪ Map.add p β (Γ ∪ Δ)
         ≃
      (Γ ∪ Δ) ∪ (Γ' ∪ Map.add p β Δ).
  Proof.
    intros Γ Γ' Δ p β p_fresh Γ_Δ Γ'_ΓpΔ.
    apply Joinable_Equal_1.
    split. intros H.
    apply join_in in H. destruct H.
    apply join_in2. apply join_in1. auto.
    apply F.add_in_iff in H. destruct H.
    apply join_in2. apply join_in2. apply F.add_in_iff. left. auto.
    apply join_in1. auto.
    intros H.
    apply join_in in H. destruct H.
    apply join_in2. apply F.add_in_iff. right. auto.
    apply join_in in H. destruct H.
    apply join_in1. auto.
    apply F.add_in_iff in H. destruct H.
    apply join_in2. apply F.add_in_iff. left. auto.
    apply join_in2. apply F.add_in_iff. right. apply join_in2. auto.
    apply Joinable_join_intro_l.
    apply Joinable_join_intro_r. eapply Join_fresh_add_prop. apply p_fresh.
    apply Γ'_ΓpΔ.
    apply Joinable_join_intro_r. apply Joinable_refl.
    apply joinable_comm. apply Join_add_prop.
    eapply Join_add_prop'''. apply Γ'_ΓpΔ.
    apply (Join_fresh_add_prop p_fresh) in Γ'_ΓpΔ.
    apply joinable_comm. apply comp_join_elim_r with (Δ:=Γ). auto. apply Γ'_ΓpΔ.
    apply Joinable_join_intro_r. apply Join_add_prop.
    apply Joinable_fresh. auto. apply Joinable_refl.
    apply Joinable_join_intro_r. auto.
    apply Join_add_prop''.
    apply Joinable_join_intro_l. auto. apply Joinable_refl.
  Qed.

  Lemma wf_add : forall (Γ : Heap) p ik η,
      heap_wf Γ ->
      Included _ (env_ptr η) (key_set Γ) ->
      heap_wf (Map.add p (ik, η) Γ).
  Proof.
    intros Γ p ik η Γwf η_Γ.
    split. intros q q_in.
    destruct q_in. auto.
    destruct H as [k [i' [η' [? ?]]]].
    apply F.add_mapsto_iff in H. destruct H. destruct H.
    inversion H1.
    apply F.add_in_iff. right. apply η_Γ. rewrite -> H4. auto.
    apply F.add_in_iff. right.
    apply Γwf.
    apply Union_intror. exists k, i', η'. destruct H. auto.
    intros q q_in. 
    apply Union_introl. auto.
  Qed.

End Machine.

(* Local Variables: *)
(* company-coq-local-symbols: (("~>" . ?↣)) *)
(* End: *)
