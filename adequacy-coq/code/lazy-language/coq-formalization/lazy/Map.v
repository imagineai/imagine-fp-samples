Set Automatic Coercions Import.
Set Implicit Arguments.

Require Import Utf8.
Require Import List.
Require Export FMapInterface.
Require Export FMapWeakList.
Require Export FMapFacts.
Require Import Coq.Program.Equality.

Require Import Ensembles.

(** * Extensions of Stdlib FMapWeaklist (associative maps) *)

(** ** A extension of WS (Weak Signature) including new operations *)
Module Type WSfunExtended (K : DecidableType) (E : Equalities.Eq) <: WSfun K.
  Include (WSfun K).
  Definition elt := E.t.

  (** Joinable: Two heaps are equal on the shared points of their domains *)
  Parameter Joinable : t elt -> t elt -> Prop.
  Parameter Submap : t elt -> t elt -> Prop.
  (** Union of two heaps, the operation only makes sense when the heaps are joinable *)
  Parameter join : t elt -> t elt -> t elt.

  (** Some properties required for the new operations *)
  Section JoinSpec.
    Variable m1 : t elt.
    Variable m2 : t elt.
    Parameter join_sub1 : Joinable m1 m2 -> Submap m1 (join m1 m2).
    Parameter join_sub2 : Joinable m1 m2 -> Submap m2 (join m1 m2).
    Parameter join_MapsTo : forall k e, MapsTo k e (join m1 m2) -> MapsTo k e m1 \/ MapsTo k e m2.
  End JoinSpec.

End WSfunExtended.

(** ** Extension of raw maps (list of pais with no duplicates) *)
Module MapRaw (K : DecidableType).
  Include FMapWeakList.Raw K.
  Import PX.

  (** Join operation *)
  Fixpoint join {elt} (m1 : t elt) (m2 : t elt) : t elt :=
    match m1 with
      nil => m2
    | (k, e) :: m1 => (k, e) :: join m1 (remove k m2)
    end.

  (** Some lemmas about Join and MapsTo *)
  
  Lemma join_MapsTo:
    forall elt, forall m1 m2 : t elt,
        NoDupA (@eqk _) m2 ->
        forall k e,
          MapsTo k e (join m1 m2) ->
          MapsTo k e m1 \/ MapsTo k e m2.
  Proof.
    induction m1 ;
      intros m2 Q k e M1.
    simpl in *.
    right. auto.
    destruct a as [k' e'].
    simpl in *.
    unfold MapsTo in M1.
    rewrite InA_cons in M1.
    destruct M1 as [EQ | M2].
    left. auto.
    specialize (IHm1 (remove k' m2) (remove_NoDup Q k') k e M2).
    destruct IHm1 as [M3 | M4].
    left. auto.
    right.
    eapply remove_3 ;
      eauto.
  Qed.

  Lemma MapsTo_join_1:
    forall elt, forall m1 m2 : t elt,
        forall k e,
          MapsTo k e m1 ->
          MapsTo k e (join m1 m2).
  Proof.
    induction m1.
    intros m2 k e M.
    dependent destruction M.
    intros m2 k e M.
    destruct a as [k' e'].
    simpl.
    unfold MapsTo in M.
    rewrite InA_cons in M.
    destruct M as [E | M3].
    auto.
    specialize (IHm1 (remove k' m2)  _ _ M3).
    auto.
  Qed.
  
  Lemma MapsTo_InA :
    forall elt, forall m : t elt,
        forall k e,
          MapsTo k e m ->
          InA (@eqk _) (k, e) m.
  Proof.
    intros. auto.
  Qed.
  
  Lemma InA_join_1:
    forall elt, forall m1 : t elt,
        NoDupA (@eqk _) m1 ->
        forall m2 : t elt,
          NoDupA (@eqk _) m2 ->
          forall k e,
            InA (@eqk _) (k, e) (join m1 m2) ->
            InA (@eqk _) (k, e) m1 \/ InA (@eqk _) (k, e) m2.
  Proof.
    induction 1 as [ | [k' e'] m1 NIn Hdup0 Hip] ;
      intros m2 Hdup1 k e H'.
    simpl in *.
    right. auto.
    simpl in *.
    dependent destruction H'.
    left. constructor. auto.
    specialize (Hip _ (remove_NoDup Hdup1 k') k e H').
    destruct Hip as [H0 | H1].
    left. eapply InA_cons_tl. auto.
    right.
    eapply remove_3'.
    auto.
    eauto.
  Qed.

  Lemma InA_remove:
    forall elt m1,
      NoDupA (@eqk elt) m1  ->
      forall k k' e, K.eq k k'
                ->  ~ InA (@eqk _) (k, e) (remove k' m1).
  Proof.
    intros elt m1 nodup k k' e EQ.
    intro H.
    assert (In k (remove k' m1)) as In0.
    rewrite In_alt.
    exists e. auto.
    contradict In0.
    eapply remove_1.
    auto.
    eapply K.eq_sym.
    auto.
  Qed.

  Lemma join_NoDup :
    forall elt,
    forall m1, NoDupA (@eqk elt) m1 ->
          forall m2, NoDupA (@eqk elt) m2 ->
                NoDupA (@eqk elt) (join m1 m2).
  Proof.
    induction 1 as [ | [k e] m1 nin nodup Hip nodup2].
    simpl.
    tauto.
    intros m2 nodup2.
    simpl.
    constructor.
    intro N.
    set (H := InA_join_1 nodup (remove_NoDup nodup2 k) N).
    clearbody H.
    destruct H as [H0 | H1].
    contradiction.
    contradict H1.
    eapply InA_remove.
    eapply nodup2.
    eapply K.eq_refl.
    eapply Hip.
    eapply remove_NoDup.
    auto.
  Qed.

  Lemma In_nil:
    forall elt k, ~ In k (nil : t elt).
  Proof.
    intros elt k.
    intro In1.
    destruct In1 as [e M].
    contradict M.
    eapply empty_1.
  Qed.
    
  Lemma join_in1:
    forall elt,
    forall m1 m2 : t elt,
    forall k,
      In k m1 ->
      In k (join m1 m2).
  Proof.
    intros elt m1 m2 k I.
    destruct I as [e M].
    set (H := MapsTo_join_1 m2 M).
    eexists. eauto.
  Qed.    

  Lemma join_in2:
    forall elt,
    forall m1 m2 : t elt,
      NoDupA (@eqk elt) m2 ->
    forall k,
      In k m2 ->
      In k (join m1 m2).
  Proof.
    induction m1.
    intros m2 Q k In2.
    simpl. auto.
    intros m2 Q k In2.
    destruct a as [k' e].
    simpl.
    destruct (K.eq_dec k' k) as [EQ | NEQ].
    exists e. auto.
    specialize (IHm1 (remove k' m2) (remove_NoDup Q k') k).
    destruct In2 as [e' M].
    set (H := remove_2 Q NEQ M).
    clearbody H.
    assert (In k (remove k' m2)) as In2.
    exists e'. auto.
    specialize (IHm1 In2).
    clear - IHm1 NEQ.
    destruct IHm1 as [e' M].
    exists e'. auto.
  Qed.

  Lemma MapsTo_join_2_aux1:
    forall elt,
    forall m1 m2 : t elt,
      NoDupA (@eqk elt) m2 ->
    forall k,
      ~ In k m1 ->
      forall e,
        MapsTo k e m2 ->
        MapsTo k e (join m1 m2).
  Proof.
    induction m1 ;
    intros m2 D k Q e M.
    simpl. auto.
    destruct a as [k' e'].
    simpl.
    destruct (K.eq_dec k k') as [E | NE].
    auto.
    contradict Q.
    exists e'. auto.
    assert (~ In k m1) as Q'.
    intro Q'. contradict Q.
    destruct Q' as [e0 M0].
    exists e0. auto.
    assert (MapsTo k e (remove k' m2)) as M1.
    eapply remove_2 ; auto.
    specialize (IHm1 (remove k' m2) (remove_NoDup D k') k Q' e M1).
    auto.
  Qed.
  
End MapRaw.

(** * Extended Map module *)
(** The WSfun signature of the standard library has been extended to support the new opperations *)
Require Structures.Equalities.

Module MakeMap (K : DecidableType) (E : Equalities.EqualityType) <: WSfunExtended K E.

  Module Map := FMapWeakList.Make K.
  Include Map.
  Module MapRaw := MapRaw K.
  Module Export MapFacts := FMapFacts.WProperties_fun K Map.
  
  Notation key_eq := K.eq.

  Definition elt := E.t.

  (** Two map are joinable if they match on common keys *)
  Section JoinableDef.
    Variable m1 : t elt.
    Variable m2 : t elt.
    Definition Joinable : Prop :=
      forall k e e', MapsTo k e m1 -> MapsTo k e' m2 -> E.eq e e'.
  End JoinableDef.

  (** Notion of Submap *)
  Section SubmapDef.
    Variable m1 : t elt.
    Variable m2 : t elt.
    Definition Submap := (forall k, In k m1 -> In k m2) /\ Joinable m1 m2.
  End SubmapDef.

  Hint Unfold Joinable Submap.

  Section JoinDef.
    Definition join (m1 : t elt) (m2 : t elt)
      := Build_slist (MapRaw.join_NoDup m1.(NoDup) m2.(NoDup)).
  End JoinDef.

  Definition heap_eq := Equiv E.eq.
  Definition singleton (p : key) elt (e : elt) := add p e (empty _).

  Notation "map1 ∪ map2" := (join map1 map2) (at level 50, left associativity).
  Notation "map1 ⋈ map2" := (Joinable map1 map2) (at level 70, no associativity).
  Notation "⎨ p ⤇ e ⎬" := (singleton p  e) (at level 65, no associativity).

  (** Main properties of Joinable operation *)
  Section JoinSpec.
    Variable m1 : MakeMap.t elt.
    Variable m2 : MakeMap.t elt.

    Lemma joinable_comm: m1 ⋈ m2 <-> m2 ⋈ m1.
    Proof.
      firstorder.
    Qed.

    Lemma join_MapsTo :
      forall k e, MakeMap.MapsTo k e (m1 ∪ m2) -> MakeMap.MapsTo k e m1 \/ MakeMap.MapsTo k e m2.
    Proof.
      intros k e M.
      eapply MapRaw.join_MapsTo.
      eapply m2.
      auto.
    Qed.
    
    Lemma join_in :
      forall k, MakeMap.In k (m1 ∪ m2) -> MakeMap.In k m1 \/ MakeMap.In k m2.
    Proof.
      intros k M1.
      destruct M1 as [e' M].
      set (H := MapRaw.join_MapsTo m1.(this) m2.(NoDup) M).
      destruct H as [ L | E].
      left. eexists. eauto.
      right. eexists. eauto.
    Qed.

    Lemma join_in1 :
      forall k, MakeMap.In k m1 -> MakeMap.In k (m1 ∪ m2).
    Proof.
      intros k.
      eapply MapRaw.join_in1.
    Qed.

    Lemma join_in2 :
      forall k, MakeMap.In k m2 -> MakeMap.In k (m1 ∪ m2).
    Proof.
      intros k.
      eapply MapRaw.join_in2.
      eapply m2.
    Qed.
      
    Lemma joinable_join1 : m1 ⋈ m2 -> m1 ⋈ (m1 ∪ m2).
    Proof.
      intros Hjble.
      intros k e e' M1 M.
      set (H := MapRaw.join_MapsTo m1.(this) m2.(NoDup) M).
      destruct H as [L | E].
      set (E := MapFacts.F.MapsTo_fun M1 L).
      rewrite E.
      apply E.eq_equiv.
      eapply Hjble ;
      eauto.
    Qed.

    Lemma joinable_join2 : m1 ⋈ m2 -> m2 ⋈ (m1 ∪ m2).
    Proof.
      intros Hjble.
      intros k e e' M1 M.
      set (H := MapRaw.join_MapsTo m1.(this) m2.(NoDup) M).
      destruct H as [L | E].
      rewrite joinable_comm in Hjble.
      eapply Hjble. eauto. eauto.
      set (H' := MapFacts.F.MapsTo_fun M1 E).
      rewrite H'.
      apply E.eq_equiv.
    Qed.
    
    Lemma join_sub1 : m1 ⋈ m2  -> Submap m1 (m1 ∪ m2).
    Proof.
      intro Hjble.
      split.
      intro k.
      eapply MapRaw.join_in1.
      eapply joinable_join1.
      auto.
    Qed.

    Lemma join_sub2 : m1 ⋈ m2 -> Submap m2 (m1 ∪ m2).
    Proof.
      intro Hjble.
      split.
      intro k.
      eapply MapRaw.join_in2.
      eapply m2.
      eapply joinable_join2.
      auto.
    Qed.
    
  End JoinSpec.

  Import Ensembles.
  
  Definition SetIn := Ensembles.In.
  
  Definition KeySet := Ensemble K.t.

  (** Domain of a map *)
  Definition key_set (m : Map.t elt) : KeySet := fun k => Map.In k m.

  Lemma key_set_find_in:
    forall m k e, Map.find k m = Some e -> Ensembles.In _ (key_set m) k.
  Proof.
    intros m k e F.
    eexists.
    eapply Map.find_2.
    eauto.
  Qed.

  (** Auxiliar tactics to resolve MapsTo-related goals *)
  
  Ltac destruct_MapsTo_join H1 H2 :=
    match goal with
      [ Q : MapsTo ?k ?e (?Γ ∪ ?Δ) |- _ ] =>
      let H := fresh "H" in
      set (H := join_MapsTo Q) ;
      clearbody  H ;
      destruct H as [H1 | H2] ;
      clear Q
    end.

  Ltac destruct_MapsTo_join' :=
    let H := fresh "H" in
    let H' := fresh "H'" in
    destruct_MapsTo_join H H'.

  Ltac solve_elem_eq :=
    match goal with
      [H : MapsTo ?k ?e ?Γ,
           H' : MapsTo ?k ?e' ?Δ,
                H1 : ?Γ ⋈ ?Δ |- E.eq ?e ?e'] =>
      eapply H1 ; eauto
    |  [H : MapsTo ?k ?e ?Γ,
            H' : MapsTo ?k ?e' ?Δ,
                H1 : ?Δ ⋈ ?Γ |- E.eq ?e ?e'] =>
       rewrite joinable_comm in H1 ;
       eapply H1 ; eauto
    | [H : MapsTo ?k ?e ?Γ,
           H': MapsTo ?k ?e' ?Γ |- E.eq ?e ?e'] =>
      rewrite (F.MapsTo_fun H H') ;
      eapply E.eq_equiv
    end.

  Ltac destruct_In_join H1 H2 :=
    match goal with
      [ Q : MakeMap.In ?k (?Γ ∪ ?Δ) |- _ ] =>
      let H := fresh "H" in
      set (H := join_in Q) ;
      clearbody  H ;
      destruct H as [H1 | H2] ;
      clear Q
    end.

  Ltac destruct_In_join' :=
    let H := fresh "H" in
    let H' := fresh "H'" in
    destruct_In_join H H'.

  Ltac solve_in_join :=
    match goal with
    | [H: MakeMap.In ?k ?Γ  |- MakeMap.In ?k ?Γ ] => assumption
    | [H: MakeMap.In ?k ?Γ  |- MakeMap.In ?k (?Γ ∪ ?Δ) ] =>
      eapply join_in1 ; eauto
    | [H : MakeMap.In ?k ?Δ |- MakeMap.In ?k (?Γ ∪ ?Δ) ] =>
      eapply join_in2 ; eauto
    | [H : MakeMap.In ?k ?Γ |- MakeMap.In ?k (?Γ' ∪ (?Δ ∪ ?Δ'))] =>
      eapply join_in2 ; try solve_in_join
    | [H : MakeMap.In ?k ?Γ |- MakeMap.In ?k ((?Γ' ∪ ?Δ) ∪ ?Δ')] =>
      eapply join_in1 ; try solve_in_join
    end.

  Lemma Submap_MapsTo:
    forall Γ Γ' k e,
      Submap Γ Γ' ->
      MapsTo k e Γ -> exists e', E.eq e e' /\ MapsTo k e' Γ'.
  Proof.
    intros Γ Γ' k e S1 M1.
    destruct S1 as [H Hjble].
    assert (MakeMap.In k Γ) as I.
    eexists. exact M1.
    specialize (H k I).
    destruct H as [e' M2].
    exists e'.
    split.
    eapply Hjble ; eauto.
    auto.
  Qed.
                                                                                                                             
  Lemma Joinable_refl:
    forall Γ, Γ ⋈ Γ.
  Proof.
    intros Γ.
    intros k e e' M1 M2.
    solve_elem_eq.
  Qed.

  Lemma Joinable_join_comm:
    forall Γ Δ, Γ ⋈ Δ -> Γ ∪ Δ ⋈ Δ ∪ Γ.
  Proof.
    intros Γ Δ Hjble.
    intros k e e' M1 M2.
    repeat destruct_MapsTo_join' ;
      solve_elem_eq.
  Qed.

  Lemma Joinable_join_intro_r:
    forall Γ Δ Δ', Γ ⋈ Δ -> Γ ⋈ Δ' -> Γ ⋈ (Δ ∪ Δ').
  Proof.
    intros Γ Δ Δ' Hjble1 Hjble2.
    intros k e e' M1 M2.
    destruct_MapsTo_join H1 H2 ;
      solve_elem_eq.
  Qed.

  Lemma Joinable_join_intro_l:
    forall Γ Δ Δ', Δ ⋈ Γ -> Δ' ⋈ Γ -> Δ ∪ Δ' ⋈ Γ.
  Proof.
    intros Γ Δ Δ' Hjble1 Hjble2.
    intros k e e' M1 M2.
    destruct_MapsTo_join H1 H2 ;
      solve_elem_eq.
  Qed.

  Lemma Joinable_submap:
    forall Γ' Γ Δ, Γ ⋈ Δ -> Submap Γ' Γ -> Γ' ⋈ Δ.
  Proof.
    intros Γ Δ Δ' Hjble1 submap.
    intros k e e' M1 M2.
    set (H := Submap_MapsTo submap M1).
    destruct H as [e0 [EQ0 M3]].
    rewrite EQ0.
    solve_elem_eq.
  Qed.
  
  Lemma Joinable_submap_2:
    forall Γ' Δ, Submap Γ' Δ -> Γ' ⋈ Δ.
  Proof.
    intros Γ' Δ.
    intro.
    destruct H as [H1 H2].
    auto.
  Qed.
   
  Lemma Joinable_join_elim_1:
    forall  Γ Δ Δ', Γ ⋈ Δ -> Γ ∪ Δ ⋈ Δ' -> Γ ⋈ Δ'.
  Proof.
    intros Γ Δ Δ' Hjble1 Hjble2.
    eapply Joinable_submap.
    eauto.
    eapply join_sub1.
    auto.
  Qed.

  Lemma Joinable_join_elim_2:
    forall  Γ Δ Δ', Γ ⋈ Δ -> Γ ∪ Δ ⋈ Δ' -> Δ ⋈ Δ'.
  Proof.
    intros Γ Δ Δ' Hjble1 Hjble2.
    eapply Joinable_submap.
    eauto.
    eapply join_sub2.
    auto.
  Qed.

  Lemma Joinable_join_assoc_1:
    forall Γ Δ Δ',
      Γ ⋈ Δ -> Γ ⋈ Δ' -> Δ ⋈ Δ' ->
      (Γ ∪ Δ) ∪ Δ' ⋈ Γ ∪ (Δ ∪ Δ').
  Proof.
    intros Γ Δ Δ' Hjble1 Hjble2 Hjble3.
    intros k e e' M1 M2.
    repeat destruct_MapsTo_join';
    try solve_elem_eq.
  Qed.

  Ltac destruct_join_joinable :=
    match goal with
    | [H0 : ?Γ ⋈ ?Δ, H : ?Γ ∪ ?Δ ⋈ ?Γ' |- _] =>
     let H1 := fresh "H1" in
      let H2 := fresh "H2" in
      set (H1 := Joinable_join_elim_1 H0 H) ;
      set (H2 := Joinable_join_elim_2 H0 H) ;
      clearbody H1 ;
      clearbody H2 ;
      clear H
    end.    

End MakeMap.

Require Import SetoidList.
Require Import Coq.Classes.RelationPairs.
Require Import Coq.Structures.Equalities.

(** Backport from new to old version of EqualityType. *)
(* Coq's map library uses some deprecated orders and equalities definitions
that will be updated on a future version of the library called MMaps (as MSets
replaced the old FSets).*)
Module EqCompat (E : Equalities.EqualityType) <: Equalities.EqualityTypeOrig.
  Definition t := E.t.
  Definition eq := E.eq.

  Lemma eq_refl: forall x, eq x x.
    eapply E.eq_equiv.
  Qed.

  Lemma eq_sym: forall x y, eq x y -> eq y x.
    eapply E.eq_equiv.
  Qed.

  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
    eapply E.eq_equiv.
  Qed.
  
End EqCompat.

(** ** Equivalence relation over lists *)
Module ListEq (E : Equalities.EqualityType) <: Equalities.EqualityType.
  Definition t := list E.t.
  Definition eq := eqlistA E.eq.

  Lemma eq_equiv : Equivalence eq.
    eapply eqlistA_equiv.
    eapply E.eq_equiv.
  Qed.
End ListEq.

(** ** Equivalence relation over pairs *)
Module PairEq (E1 : Equalities.EqualityType) (E2 : Equalities.EqualityType).
  Definition t := (E1.t * E2.t)%type.
  Definition eq := (E1.eq * E2.eq)%signature.
  Lemma eq_equiv : Equivalence eq.
    split.
    - intros (a, b). split.
      eapply E1.eq_equiv.
      eapply E2.eq_equiv.
    - intros (a, b) (a', b') H.
      split.
      cbv.
      eapply (E1.eq_equiv.(@Equivalence_Symmetric _ _)).
      eapply H.
      cbv.
      eapply (E2.eq_equiv.(@Equivalence_Symmetric _ _)).
      eapply H.
    - intros (x, x') (y, y') (z, z') EQ1 EQ2.
      split.
      cbv.
      eapply E1.eq_equiv.(@Equivalence_Transitive _ _).
      eapply EQ1.
      simpl.
      eapply EQ2.
      eapply E2.eq_equiv.(@Equivalence_Transitive _ _).
      eapply EQ1.
      simpl.
      eapply EQ2.
  Qed.
End PairEq.

(** ** Heaps are maps [Pointer -> (Element, PointerList)] *)
(** Equality on pointers needs to be decidable. We require an 
equality for elements to cope with the Joinable operation *)
Module Heap (PointerType : DecidableTypeOrig) (E : Equalities.EqualityType).
  Definition Pointer : Type := PointerType.t.
  Definition elt := E.t.
  Definition elt_pair := (elt * list Pointer)%type.
  Module PointerTypeU := Update_DT PointerType.
  Module PointerListEq := ListEq PointerTypeU.
  Module EltPairEq := PairEq E PointerListEq.
  Module Export Map  := MakeMap PointerType EltPairEq.

  Definition Heap := Map.t elt_pair.
End Heap.

(** ** Heaps with Leibniz equality for both pointers and elements *)
(* Leibniz equality for pointers is necessary since we will work with
   Coq.Ensembles library to represent sets. In particular, we have the function
   [key_set] that that represets the domain of a Heap (a set of pointers).
   Consider two singleton heaps H1 = [p -> (i, η)] and H2 = [p' -> (i', η']]
   where [p==p']. If [==] is not Leibniz we cannot prove
   Same_set _ (key_set (H1)) (key_set (H2)).
   An alternative to Ensembles is Coq.MSets (finite sets). It requires a decidable
   order for the elements of the set. It is not easy to obtain a decidable
   equality for Heaps (Maps) that would allow us to represet sets of
   "configurations" [Γ, α, e, s]. For that reason I decided not to use MSets.
*)
Module UsualHeap (PointerType : UsualDecidableType) (ElementType : Typ).

  Module Eq <: Equalities.EqualityType.
    Definition t := ElementType.t.
    Definition eq := Logic.eq (A := ElementType.t).
    Lemma eq_equiv: Equivalence eq.
      auto.
    Qed.
  End Eq.

  Module PointerTypeB := Backport_DT PointerType.
  Module Export Heap := Heap PointerTypeB Eq.
  Notation "map1 ≃ map2" := (Equal map1 map2) (at level 70, no associativity).

  Lemma eqlistA_leibniz:
    forall A (xs ys : list A), eqlistA Logic.eq xs ys -> xs = ys.
  Proof.
    induction xs  ;
    intros ys ;
    intros EQ ;
    dependent destruction EQ ;
    auto.
    f_equal.
        eapply IHxs.
    auto.
  Qed.
  
  Lemma heap_eq_Equiv:
      forall Γ Γ', heap_eq Γ Γ' -> Equiv Logic.eq Γ Γ'.
  Proof.
    intros Γ Γ' EQ.
    destruct EQ as [H0 H1].
    split.
    auto.
    intros k [i η] [i' η'] Hm1 Hm2.
    specialize (H1 _ _ _ Hm1 Hm2).
    cbv in H1.
    destruct H1 as [L1 L2].
    rewrite L1.
    f_equal.
    eapply eqlistA_leibniz.
    auto.
  Qed.
    
  Lemma heap_Equiv_eq:
    forall Γ Γ', Equiv Logic.eq Γ Γ' -> heap_eq Γ Γ'.
  Proof.
    intros Γ Γ' EQ.
    destruct EQ as [H0 H1].
    split.
    auto.
    intros k [i η] [i' η'] Hm1 Hm2.
    specialize (H1 _ _ _ Hm1 Hm2).
    rewrite H1.
    reflexivity.
  Qed.

  Lemma heap_Equiv:
    forall Γ Γ', heap_eq Γ Γ' <-> Equiv Logic.eq Γ Γ'.
  Proof.
    intros Γ Γ'.
    split.
    apply heap_eq_Equiv.
    apply heap_Equiv_eq.
  Qed.

  Lemma heap_Equal:
    forall Γ Γ', heap_eq Γ Γ' <-> Equal Γ Γ'.
  Proof.
    intros Γ Γ'.
    rewrite heap_Equiv.
    rewrite F.Equal_Equiv.
    tauto.
  Qed.

  Lemma pair_eq_leibniz:
    forall e e', EltPairEq.eq e e' -> e = e'.
  Proof.
    intros e e' EQ.
    destruct e.
    destruct e'.
    cbv in EQ.
    destruct EQ as [EQ0 EQ1].
    rewrite EQ0.
    set (H := eqlistA_leibniz EQ1).
    rewrite H.
    auto.
  Qed.

  Lemma Equal_key_set:
    forall Γ Δ, Γ ≃ Δ -> Ensembles.Same_set _ (key_set Γ) (key_set Δ).
  Proof.
    intros Γ Δ EQ.
    rewrite F.Equal_Equiv in EQ.
    split.
    - intros k I1.
      eapply EQ.
      auto.
    - intros k I2.
      eapply EQ.
      auto.
  Qed.

  Lemma Joinable_Equal_1:
    forall Γ Γ',
      (forall k, In k Γ <-> In k Γ') ->
      Γ ⋈ Γ' ->
      Γ ≃ Γ'.
  Proof.
    intros.
    rewrite F.Equal_Equiv.
    split.
    auto.
    unfold Joinable in H0.
    intros.
    eapply pair_eq_leibniz.
    eapply H0 ; eauto.
  Qed.

  Lemma Join_comm_1:
    forall Γ Δ, Γ ⋈ Δ -> Γ ∪ Δ ≃ Δ ∪ Γ.
  Proof.
    intros Γ Δ Hjble.
    eapply Joinable_Equal_1.
    split ; intros ;
    repeat destruct_In_join' ;
    solve_in_join.
    eapply Joinable_join_comm ;
      eauto.
  Qed.
  
  Lemma Join_assoc_1:
    forall Γ Δ Δ',
      Γ ⋈ Δ -> Γ ⋈ Δ' -> Δ ⋈ Δ' ->
      (Γ ∪ Δ) ∪ Δ' ≃ Γ ∪ (Δ ∪ Δ').
  Proof.
    intros Γ Δ Δ' Hjble0 Hjble1 Hjble2.
    eapply Joinable_Equal_1.
    split ; intros ;
    repeat destruct_In_join' ;
    solve_in_join.
    eapply Joinable_join_assoc_1 ;
      eauto.
  Qed.

  Lemma Join_idem:
    forall Γ, Γ ∪ Γ ≃ Γ.
  Proof.
    intros Γ.
    eapply Joinable_Equal_1.
    split ; intros ;
    repeat destruct_In_join' ;
    solve_in_join.
    intros k e e' M1 M2.
    destruct_MapsTo_join' ;
    solve_elem_eq.
  Qed.

  Add Parametric Morphism : Joinable with
      signature Equal ==> Equal ==> iff as Equal_joinable_mor.
  Proof.
    intros Γ0 Γ1 EQ Δ0 Δ1 EQ'.
    split.
    intro H.
    intros k e e' M1 M2.
    rewrite <- EQ in M1.
    rewrite <- EQ' in M2.
    solve_elem_eq.
    intro H.
    intros k e e' M1 M2.
    rewrite EQ in M1.
    rewrite EQ' in M2.
    solve_elem_eq.
  Qed.

  Add Parametric Morphism : Submap with
      signature Equal ==> Equal ==> impl as Equal_submap_mor1.
  Proof.
    intros Γ Γ' EQ.
    intros Δ Δ' EQ'.
    intro S1.
    split.
    intros k.
    intros I1.
    rewrite <- EQ in I1.
    rewrite <- EQ'.
    eapply S1.
    auto.
    rewrite <- EQ.
    rewrite <- EQ'.
    eapply S1.
  Qed.

  Add Parametric Morphism : Submap with
      signature Equal ==> Equal ==> iff as Equal_submap_mor.
  Proof.
    intros Γ Γ' EQ.
    intros Δ Δ' EQ'.
    split.
    rewrite EQ.
    rewrite EQ'.
    trivial.
    rewrite EQ.
    rewrite EQ'.
    trivial.
  Qed.
    
  Lemma Equal_join_mor:
    forall Γ Δ Γ' Δ', Γ ⋈ Δ ->  Γ ≃ Γ' -> Δ ≃ Δ' -> Γ ∪ Δ ≃ Γ' ∪ Δ'.
  Proof.
    intros Γ Δ Γ' Δ' Hjble EQ1 EQ2.
    eapply Joinable_Equal_1.
    split ; intros ;
    repeat destruct_In_join'.
    eapply join_in1.
    rewrite <- EQ1. auto.
    eapply join_in2.
    rewrite <- EQ2. auto.
    eapply join_in1.
    rewrite EQ1. auto.
    eapply join_in2.
    rewrite EQ2. auto.
    intros k e e' M1 M2.
    repeat destruct_MapsTo_join'.
    rewrite EQ1 in H0.
    solve_elem_eq.
    rewrite <- EQ1 in H.
    solve_elem_eq.
    rewrite <- EQ2 in H'.
    solve_elem_eq.
    rewrite <- EQ2 in H'.
    solve_elem_eq.
  Qed.

  Lemma Submap_MapsTo_leibniz:
    forall Γ Γ' k e,
      Submap Γ Γ' ->
      MapsTo k e Γ ->
      MapsTo k e Γ'.
  Proof.
    intros Γ Γ' k [i1 l1] S1 M1.
    set (X := Submap_MapsTo S1 M1).
    clearbody X.
    destruct X as [[i2 l2] [EQ M2]].
    cbv in EQ.
    rewrite (proj1 EQ).
    rewrite (eqlistA_leibniz (proj2 EQ)).
    auto.
  Qed.

  Lemma find_submap:
    forall Γ Δ p α,
      Submap Γ Δ ->
      find p Γ = Some α ->
      find p Δ = Some α.
  Proof.
    intros Γ Δ p α S1 F1.
    rewrite <- F.find_mapsto_iff in F1.
    rewrite <- F.find_mapsto_iff.
    eapply Submap_MapsTo_leibniz ;
      eauto.
  Qed.

  Lemma find_Equal:
    forall Γ Δ : t elt, forall p α,
      Γ ≃ Δ ->
      find p Γ = Some α ->
      find p Δ = Some α.
  Proof.
    intros Γ Δ.
    intros p α EQ F1.
    rewrite <- F.find_mapsto_iff in F1.
    rewrite <- F.find_mapsto_iff.
    rewrite <- EQ.
    auto.
  Qed.

  Lemma MapsTo_singleton:
    forall p α, MapsTo p α (⎨ p ⤇ α ⎬ : t elt).
  Proof.
    intros p e.
    unfold singleton.
    eapply add_1.
    auto.
  Qed.
      
  Lemma find_submap_singleton:
    forall Γ p α, Γ ⋈ ⎨ p ⤇ α ⎬ -> Submap (⎨ p ⤇ α ⎬) (Γ ∪ ⎨ p ⤇ α ⎬).
  Proof.
    intros Γ p α Hjble.
    split.
    intros k I.
    destruct I as [e' I'].
    cbn in I'.
    dependent destruction I'.
    cbv in H.
    destruct H as [H1 H2].
    assert (k = p) as R.
    auto.
    subst.
    eapply join_in2.
    exists α. simpl. auto.
    dependent destruction I'.
    rewrite joinable_comm.
    eapply Joinable_join_intro_l.
    auto.
    eapply Joinable_refl.
  Qed.    
    
  Lemma find_Joinable_singleton_1:
    forall Γ p α,
      Γ ⋈ ⎨ p ⤇ α ⎬  ->
      find p (Γ ∪ ⎨ p ⤇ α ⎬) = Some α.
  Proof.
    intros Γ p α F.
    rewrite <- F.find_mapsto_iff.
    assert (Submap (⎨ p ⤇ α ⎬) (Γ ∪ ⎨ p ⤇ α ⎬)).
    eapply find_submap_singleton. auto.
    eapply Submap_MapsTo_leibniz.
    eauto.
    eapply MapsTo_singleton.
  Qed.

  Lemma find_singleton_Joinable:
    forall Γ p α,
      find p Γ = Some α ->
      Γ ⋈ ⎨ p ⤇ α ⎬.
  Proof.
    intros Γ p α F1.
    intros k e e' M1 M2.
    rewrite <- F.find_mapsto_iff in F1.
    unfold MapsTo in M2.
    simpl in M2.
    dependent destruction M2.
    cbv in H.
    destruct H as [H1 H2].
    rewrite H1 in M1.
    set (H3 := F.MapsTo_fun F1 M1).
    rewrite H2.
    rewrite <- H3.
    reflexivity.
    dependent destruction M2.
  Qed.

  Lemma find_singleton_Join:
    forall Γ p α,
      find p Γ = Some α ->
      Γ ≃ Γ ∪ ⎨ p ⤇ α ⎬.
  Proof.
    intros Γ p α F.
    eapply Joinable_Equal_1.
    intros k.
    split ; intros ;
    repeat destruct_In_join' ;
    try solve_in_join.
    destruct H' as [e H].
    cbn in H.
    dependent destruction H.
    cbv in H.
    destruct H as [E1 E2].
    subst.
    rewrite <- F.find_mapsto_iff in F.
    eexists. eauto.
    dependent destruction H.
    eapply Joinable_join_intro_r.
    eapply Joinable_refl.
    eapply find_singleton_Joinable.
    auto.
  Qed.

  Lemma Join_add:
    forall Γ p α,
      Γ ⋈ ⎨ p ⤇ α ⎬ ->
      Γ ∪ (⎨ p ⤇ α ⎬) ≃ add p α Γ.
  Proof.
    intros Γ p α Hjble.
    eapply Joinable_Equal_1.
    intros k.
    split.
    intro I1.
    destruct_In_join H1 H2.
    rewrite F.add_in_iff.
    right. auto.
    destruct H2 as [e' H3].
    dependent destruction H3.
    cbv in H.
    destruct H as [EQ1 EQ2].
    rewrite F.add_in_iff.
    left. auto.
    dependent destruction H3.
    intro I1.
    rewrite F.add_in_iff in I1.
    destruct I1 as [EQ1 | EQ2].
    eapply join_in2.
    rewrite EQ1.
    eexists α. simpl. auto.
    eapply join_in1.
    auto.
    intros k e e' M1 M2.
    set (M3 := MapsTo_singleton p α).
    clearbody M3.
    rewrite F.add_mapsto_iff in M2.
    destruct_MapsTo_join H1 H2 ;
      destruct M2 as [[EQ0 EQ1] | [NEQ M4]] ;
      try subst ; 
      try solve_elem_eq.
  Qed.

  Lemma Joinable_not_in:
    forall Γ p α,
      ~ In p Γ ->
      Γ ⋈ ⎨ p ⤇ α ⎬.
  Proof.
    intros Γ p α NI.
    intros k e e' M1 M2.
    contradict NI.
    exists e.
    unfold MapsTo in M2.
    simpl in M2.
    dependent destruction M2.
    destruct H as [EQ0 EQ1].
    simpl in *.
    subst.
    auto.
    dependent destruction M2.
  Qed.

  Import Ensembles.
  
  Lemma Join_key_set:
    forall Γ Δ, Γ ⋈ Δ ->
           Same_set _ (key_set (Γ ∪ Δ)) (Union _ (key_set Γ) (key_set Δ)).
  Proof.
    intros Γ Δ Hjble.
    split.
    intros p In1.
    assert (Map.In p (Γ ∪ Δ)) as In1'.
    auto.
    destruct_In_join H1 H2.
    eapply Union_introl. auto.
    eapply Union_intror. auto.
    intros p In1.
    destruct In1 as [p H1 | p H2].
    unfold In in *.
    unfold key_set in *.
    solve_in_join.
    unfold In in *.
    unfold key_set in *.
    solve_in_join.
  Qed.

  (** Some hints to proof automation *)
  
  Hint Unfold Ensembles.In.
  Hint Unfold key_set.
  Hint Resolve Join_assoc_1.
  Hint Resolve Join_comm_1.
  Hint Extern 4 (?Γ ⋈ ?Δ) => rewrite joinable_comm ; assumption.
  Hint Resolve Joinable_join_intro_l.
  Hint Resolve Joinable_join_intro_r.
  
  Lemma heap_add_update_prop : forall (Γ : Heap) p β β',
      Map.add p β' (Map.add p β Γ) ≃ Map.add p β' Γ.
  Proof.
    intros Γ p β β' HH.
    apply Joinable_Equal_1.
    split. intros H.
    apply F.add_in_iff in H. destruct H.
    rewrite <- H. apply F.add_in_iff. left. auto.
    apply F.add_in_iff in H. destruct H.
    apply F.add_in_iff. left. auto.
    apply F.add_in_iff. right. auto.
    intros H.
    apply F.add_in_iff in H. destruct H.
    apply F.add_in_iff. left. auto.
    apply F.add_in_iff. right.
    apply F.add_in_iff. right. auto.
    unfold "⋈". intros k e e' H H0.
    apply F.add_mapsto_iff in H.
    apply F.add_mapsto_iff in H0.
    destruct H. destruct H0.
    destruct H. destruct H0. rewrite <- H1. rewrite <- H2.
    reflexivity.
    destruct H. destruct H0. rewrite <- H in H0. contradiction.
    destruct H0.
    destruct H. destruct H0. rewrite <- H0 in H. contradiction.
    destruct H. destruct H0.
    apply add_3 in H1.
    rewrite -> (F.MapsTo_fun H1 H2). reflexivity.
    auto.
  Qed.

  Lemma heap_add_prop : forall Γ Δ p β,
      Δ ⋈ (⎨ p ⤇ β ⎬) ->
      Γ ⋈ Δ ∪ (⎨ p ⤇ β ⎬) ->
      (Γ ∪ add p β Δ) ≃ add p β (Γ ∪ Δ).
  Proof.
    intros Γ Δ p β p_Δ Hjble.
    apply Joinable_Equal_1.
    split. intros H.
    apply join_in in H. destruct H.
    apply F.add_in_iff. right.
    apply join_in1. auto.
    apply F.add_in_iff in H. destruct H.
    apply F.add_in_iff. left. auto.
    apply F.add_in_iff. right.
    apply join_in2. auto.
    intros H.
    apply F.add_in_iff in H. destruct H.
    apply join_in2. apply F.add_in_iff. left. auto.
    apply join_in in H. destruct H.
    apply join_in1. auto.
    apply join_in2. 
    apply F.add_in_iff. right. auto.
    apply joinable_comm in Hjble.
    assert (Submap (⎨ p ⤇ β ⎬) (Δ ∪ (⎨ p ⤇ β ⎬))).
    apply find_submap_singleton. auto.
    pose (Joinable_submap Hjble H) as jsm.
    apply joinable_comm in jsm.
    apply joinable_comm in Hjble. clear H.
    pose (Join_add p_Δ) as jadd.
    assert (Γ ⋈ Δ).
    apply joinable_comm.
    eapply Joinable_join_elim_1. apply p_Δ. auto.
    assert (Γ ∪ Δ ∪ (⎨ p ⤇ β ⎬) ≃ add p β (Γ ∪ Δ)).
    apply Join_add.
    apply Joinable_join_intro_l. auto. auto.
    rewrite <- H0.
    apply Joinable_join_intro_l.
    apply Joinable_join_intro_r.
    apply Joinable_join_intro_r.
    apply Joinable_refl. auto. auto.
    rewrite <- jadd.
    apply Joinable_join_intro_l.
    apply Joinable_join_intro_r.
    apply Joinable_join_intro_r. auto. 
    apply Joinable_refl. auto.
    apply Joinable_join_intro_r.
    apply Joinable_join_intro_r. auto. auto.
    apply Joinable_refl.
  Qed.
  
  Lemma Join_add_prop : forall Γ Δ p β,
    Δ ⋈ (⎨ p ⤇ β ⎬) ->
    Γ ⋈ Δ ->
    add p β Γ ⋈ Δ.
  Proof.
    intros Γ Δ p β p_Δ Γ_Δ.
    intro k.
    intros e e' H H0.
    apply F.add_mapsto_iff in H.
    destruct H. destruct H.
    symmetry. rewrite <- H in H0.
    specialize (@p_Δ p e' e H0).
    apply p_Δ. rewrite H1. apply MapsTo_singleton.
    eapply Γ_Δ. apply H. auto.
  Qed.
  
  Lemma Join_add_prop'' : forall Γ Δ p β,
    Γ ⋈ Δ ->
    add p β Γ ⋈ add p β Δ.
  Proof.
    intros Γ Δ p β Γ_Δ.
    intros k. intros e e' H H0.
    apply F.add_mapsto_iff in H. destruct H. destruct H.
    apply F.add_mapsto_iff in H0. destruct H0. destruct H0.
    rewrite <- H1,H2. reflexivity. destruct H0. apply H0 in H. inversion H.
    apply F.add_mapsto_iff in H0. destruct H0. destruct H0.
    destruct H. apply H in H0. inversion H0. destruct H, H0.
    specialize (Γ_Δ k). apply Γ_Δ. auto. auto.
  Qed.

  Lemma heap_add_prop_idemp : forall Γ Δ p β,
      Δ ⋈ (⎨ p ⤇ β ⎬) ->
      Γ ⋈ Δ ->
      add p β (Γ ∪ Δ) ≃ (add p β (Γ ∪ Δ)) ∪ Δ.
  Proof.
    intros Γ Δ p β p_Δ Γ_Δ.
    apply Joinable_Equal_1.
    split. intros H.
    apply F.add_in_iff in H. destruct H.
    apply join_in1. apply F.add_in_iff.
    left. auto.
    apply join_in in H. destruct H.
    apply join_in1. apply F.add_in_iff. right.
    apply join_in1. auto.
    apply join_in2. auto.
    intros H.
    apply join_in in H. destruct H.
    apply F.add_in_iff in H. destruct H.
    apply F.add_in_iff. left. auto.
    apply join_in in H. destruct H.
    apply F.add_in_iff. right.
    apply join_in1. auto.
    apply F.add_in_iff. right.
    apply join_in2. auto.
    apply F.add_in_iff. right.
    apply join_in2. auto.
    apply Joinable_join_intro_r.
    apply Joinable_refl.
    apply Join_add_prop. auto.
    apply Joinable_join_intro_l. auto.
    apply Joinable_refl.
  Qed.
  
  Lemma heap_add_prop_idemp' : forall Γ Δ p β,
      Γ ⋈ (⎨ p ⤇ β ⎬) ->
      Γ ⋈ Δ ->
      add p β (Γ ∪ Δ) ≃ (add p β (Γ ∪ Δ)) ∪ Γ.
  Proof.
    intros Γ Δ p β p_Γ Γ_Δ.
    apply Joinable_Equal_1.
    split. intros H.
    apply F.add_in_iff in H. destruct H.
    apply join_in1. apply F.add_in_iff.
    left. auto.
    apply join_in in H. destruct H.
    apply join_in1. apply F.add_in_iff. right.
    apply join_in1. auto.
    apply join_in1.
    apply F.add_in_iff. right.
    apply join_in2. auto.
    intros H.
    apply join_in in H. destruct H.
    apply F.add_in_iff in H. destruct H.
    apply F.add_in_iff. left. auto.
    apply join_in in H. destruct H.
    apply F.add_in_iff. right.
    apply join_in1. auto.
    apply F.add_in_iff. right.
    apply join_in2. auto.
    apply F.add_in_iff. right.
    apply join_in1. auto.
    apply Joinable_join_intro_r.
    apply Joinable_refl.
    apply Join_add_prop. auto.
    apply Joinable_join_intro_l.
    apply Joinable_refl. auto.
  Qed.

  Lemma heap_add_join_prop' : forall Γ Δ p β,
      Γ ⋈ Δ ->
      (add p β Γ) ∪ (add p β Δ) ≃ add p β (Γ ∪ Δ).
  Proof.
    intros Γ Δ p β Γ_Δ.
    apply Joinable_Equal_1.
    split. intros H.
    apply join_in in H. destruct H.
    apply F.add_in_iff in H. destruct H.
    apply F.add_in_iff. left. auto.
    apply F.add_in_iff. right. apply join_in1. auto.
    apply F.add_in_iff in H. destruct H.
    apply F.add_in_iff. left. auto.
    apply F.add_in_iff. right. apply join_in2. auto.
    intros H.
    apply F.add_in_iff in H. destruct H.
    apply join_in1.
    apply F.add_in_iff. left. auto.
    apply join_in in H. destruct H.
    apply join_in1.
    apply F.add_in_iff. right. auto.
    apply join_in2.
    apply F.add_in_iff. right. auto.
    apply Joinable_join_intro_l.
    apply Join_add_prop''. apply Joinable_join_intro_r.
    apply Joinable_refl. auto.
    apply Join_add_prop''. apply Joinable_join_intro_r.
    auto. apply Joinable_refl.
  Qed.

  Lemma heap_find_join_prop : forall Γ Δ p β,
      find (elt:=elt_pair) p (Γ ∪ Δ) = Some β ->
      (find p Γ = Some β) \/ (find p Δ = Some β).
  Proof.
    intros Γ Δ p β fp.
    apply F.find_mapsto_iff in fp.
    apply join_MapsTo in fp. destruct fp.
    left. apply find_1. auto.
    right. apply find_1. auto.
  Qed.

  Lemma heap_find_join_prop' : forall Γ Δ p β,
      Γ ⋈ Δ ->
      (find p Γ = Some β) \/ (find p Δ = Some β) ->
      find (elt:=elt_pair) p (Γ ∪ Δ) = Some β.
  Proof.
    intros Γ Δ p β Γ_Δ fp.
    apply F.find_mapsto_iff.
    destruct fp.
    apply Submap_MapsTo_leibniz with (Γ:=Γ).
    apply join_sub1. auto.
    apply F.find_mapsto_iff. auto.
    apply Submap_MapsTo_leibniz with (Γ:=Δ).
    apply join_sub2. auto.
    apply F.find_mapsto_iff. auto.
  Qed.
  
  Lemma Join_add_prop''' : forall Γ Δ p β,
      Γ ⋈ Map.add p β Δ ->
      Γ ⋈ (⎨ p ⤇ β ⎬).
  Proof.
    intros Γ Δ p β Γ_pΔ.
    intro k. intros e e' H H0.
    destruct Γ_pΔ with (k:=k) (e:=e) (e':=e').
    auto. apply F.add_mapsto_iff in H0.
    destruct H0. destruct H0. rewrite <- H1.
    apply add_1. auto. destruct H0.
    inversion H1.
    auto.
  Qed.

  Lemma comp_join_elim_l : forall Γ Δ Σ, Δ ⋈ Σ -> Γ ⋈ Δ ∪ Σ → Γ ⋈ Δ.
  Proof.
    intros Γ Δ Σ jbl jbl_union.
    intros k e e' inΓ inΔ.
    apply (@jbl_union k e e' inΓ).
    eapply Submap_MapsTo_leibniz.
    apply join_sub1; assumption. assumption.
  Qed.

  Lemma comp_join_elim_r : forall Γ Δ Σ, Δ ⋈ Σ -> Γ ⋈ Δ ∪ Σ → Γ ⋈ Σ.
  Proof.
    intros Γ Δ Σ jbl jbl_union.
    intros k e e' inΓ inΔ.
    apply (@jbl_union k e e' inΓ).
    eapply Submap_MapsTo_leibniz.
    apply join_sub2; assumption. assumption.
  Qed.

End UsualHeap.
