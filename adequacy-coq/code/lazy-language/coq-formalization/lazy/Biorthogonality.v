Add Rec LoadPath "." as Top.
Set Automatic Coercions Import.
Set Implicit Arguments.

Require Import Utf8.
Require Import Ensembles.
Require Import Sets.
Require Import Coq.Structures.Orders.
Require Import Relations Morphisms Setoid Equalities.
Require Export Basics.

(** * Galois Connections, Orthogonal operators *)
(* Rewrited from a previous version, now use modules instead of records *)

Open Scope program_scope.

(** A Poset Type *)
(** Usual Coq.Equalities.Orders ask for a [compare] decidable function that
we do not have on Ensembles. Using a type instead *)
Module Type PosetType <: EqLe.
  Declare Module E : EqualityType.
  Definition t := E.t.
  Definition eq := E.eq.
  Parameter le : t -> t -> Prop.
  Parameter le_refl : Reflexive le.
  Parameter le_trans : Transitive le.
  Parameter le_antisym : @Antisymmetric _ E.eq E.eq_equiv le.
  Parameter le_compat : Proper (eq ==> eq ==> iff) le.

  Instance PosetType_Reflexive : Reflexive le := le_refl.
  Instance PosetType_Transitive : Transitive le := le_trans.
  Instance PosetType_Antisymmetric :
    @Antisymmetric _ E.eq E.eq_equiv le := le_antisym.
  Instance PosetType_Compat : Proper (eq ==> eq ==> iff) le := le_compat.
End PosetType.

(** Antitone Galois Connections *)
Module Type GCType.
  Declare Module P : PosetType.
  Declare Module Q : PosetType.

  (* TODO: Use Notation Overloading (chapter 19, Canonical Structures *)
  Notation "p ≦ p'" := (P.le p p') (at level 70, no associativity) : P_scope.
  Notation "p == p'" := (P.eq p p') (at level 70, no associativity) : P_scope.
  Delimit Scope P_scope with P.
  
  Notation "q ≦ q'"  := (Q.le q q') (at level 70, no associativity) : Q_scope.
  Notation "q == q'" := (Q.eq q q') (at level 70, no associativity) : Q_scope.
  Delimit Scope Q_scope with Q.
  
  Parameter f : P.t -> Q.t.
  Parameter g : Q.t -> P.t.
  Parameter antitone : forall p q, (q ≦ f(p))%Q <-> (p ≦ g(q))%P.
  
End GCType.

(** The dual Galois Connections *)
Module GCDual (Import GC : GCType) <: GCType.

  Module P := GC.Q.
  Module Q := GC.P.
  Definition f := GC.g.
  Definition g := GC.f.

  Lemma antitone : forall p q, (q ≦ f(p))%P <-> (p ≦ g(q))%Q.
  Proof.
    intros p q.
    rewrite GC.antitone.
    tauto.
  Qed.
  
End GCDual.

(** Some properties of Galois Connections *)
Module GCFacts (Import GC : GCType).

  Open Scope P.
  Lemma comp_extensivity:
    forall p, p ≦ g (f p).
  Proof.
    intros p.
    rewrite <- antitone.
    reflexivity.
  Qed.

  Lemma function_antitone:
    forall p p', p ≦ p' -> (f (p') ≦ f (p))%Q.
  Proof.
    intros p p' H.
    rewrite antitone.
    transitivity p'.
    auto.
    eapply comp_extensivity.
  Qed.

  Lemma comp_equality:
    forall p, ((f ∘ g ∘ f) p == f p)%Q.
  Proof.
    intros p.
    eapply Q.le_antisym.
    eapply function_antitone.
    eapply comp_extensivity.
    unfold compose.
    rewrite antitone.
    reflexivity.
  Qed.

  Lemma function_resp:
    forall p p', p == p' -> (f p == f p')%Q.
  Proof.
    intros p p' EQ.
    eapply Q.le_antisym.
    eapply function_antitone.
    rewrite EQ.
    reflexivity.
    eapply function_antitone.
    rewrite EQ.
    reflexivity.
  Qed.
  
End GCFacts.

(** Closure operatos (extensive, monotone and idempotent functions) *)
Module Type ClosureOperator.
  Declare Module P : PosetType.

  Parameter h : P.t -> P.t.

  Notation "p ≦ q"  := (P.le p q) (at level 70, no associativity).
  Notation "p == q" := (P.eq p q) (at level 70, no associativity).
  
  Parameter extensive : forall p, p ≦ h (p).
  Parameter monotone: forall p p', p ≦ p' -> h (p) ≦ h (p').
  Parameter idemp: forall p, (h ∘ h) p  == h p.
  
End ClosureOperator.

(** Obtain a ClosureOperator from a Galois Connections *)
Module GCClosure (Import GC : GCType) <: ClosureOperator.

  Module Import GF := GCFacts GC.
  Module GD := GCDual GC.
  Module GDF := GCFacts GD.

  Module P := GC.P.
  Definition h : P.t -> P.t := g ∘ f.

  Lemma extensive: forall p, p ≦ h (p).
    intros p. cbv.
    eapply comp_extensivity.
  Qed.
  
  Lemma monotone: forall p p', p ≦ p' -> h (p) ≦ h (p').
    intros p p' H.
    cbv.
    eapply GDF.function_antitone.
    eapply function_antitone.
    auto.
  Qed.
  
  Lemma idemp: forall p, (h ∘ h) p == h (p).
    intro p.
    cbv.
    eapply GDF.function_resp.
    eapply comp_equality.
  Qed.

End GCClosure.

(** Use Ensemble.Included as the order to obtain a Poset *)
Module InclusionOrdered (T : Typ) <: PosetType.

  Module E.
    Definition t := Ensemble T.t.
    Definition eq := Same_set T.t.
    Lemma eq_equiv: Equivalence (Same_set T.t).
      split ; firstorder.
    Qed.
  End E.
  
  Definition t := Ensemble (T.t).
  Definition le := Included (T.t).
  Definition eq := Same_set (T.t).

  Hint Unfold t le eq.

  Lemma le_compat: Proper (eq ==> eq ==> iff) le.
    intros X Y EQ X' Y' EQ'.
    rewrite EQ.
    rewrite EQ'.
    tauto.
  Qed.

  Lemma le_refl: Reflexive le.
    intros X. firstorder.
  Qed.

  Lemma le_trans: Transitive le.
    intros X Y. firstorder.
  Qed.

  Lemma le_antisym: @Antisymmetric _ E.eq E.eq_equiv le.
    intros X Y. firstorder.
  Qed.
  Instance PosetType_Reflexive : Reflexive le := le_refl.
  Instance PosetType_Transitive : Transitive le := le_trans.
  Instance PosetType_Antisymmetric :
    @Antisymmetric _ E.eq E.eq_equiv le := le_antisym.
  Instance PosetType_Compat : Proper (eq ==> eq ==> iff) le := le_compat.

End InclusionOrdered.

(** We need two types (elements, tests) and a satisfability relation *)
Module Type TstElt.
  Parameter Elt : Type.
  Parameter Tst : Type.
  Parameter satif: Elt -> Tst -> Prop.
End TstElt.

(** Orthogonal operatos *)
Module OrthogonalOperators (Import T : TstElt).
  Notation "e ⊧ t" := (satif e t) (at level 70, no associativity).
  Implicit Type t : Tst.
  Implicit Type e : Elt.
  
  Definition btop (T : Ensemble Tst) : Ensemble Elt :=
    fun e => forall t, In _ T t -> e ⊧ t.
  
  Definition bbot (E : Ensemble Elt) : Ensemble Tst :=
    fun t => forall e, In _ E e -> e ⊧ t.

  Notation "X ⊤" := (btop X) (at level 40, no associativity).
  Notation "X ⊥" := (bbot X) (at level 40, no associativity).
  Notation "X ⌶" := (X ⊥ ⊤) (at level 40, no associativity).

End OrthogonalOperators.

(** Concrete Galois connections using Ensembles *)
Module EnsembleGC (T : TstElt) <: GCType.
  Module Export OO := OrthogonalOperators T.

  Module PTyp.
    Definition t := T.Elt.
  End PTyp.

  Module QTyp.
    Definition t := T.Tst.
  End QTyp.
  
  Module P := InclusionOrdered PTyp.
  Module Q := InclusionOrdered QTyp.
  
  Definition f := bbot.
  Definition g := btop.

  Lemma antitone:
    forall E0 T0, Included _ T0 (E0 ⊥) <-> Included _ E0 (T0 ⊤).
  Proof.
    intros E0 T0.
    split.
    intro I.
    intros e IE0.
    intros t IT0.
    assert (In _ (E0 ⊥) t).
    eapply I. auto.
    eapply H. auto.
    intro I.
    intros t IT0.
    intros e IE0.
    assert (In _ (T0 ⊤) e).
    eapply I. auto.
    eapply H.
    auto.
  Qed.
        
End EnsembleGC.

(** Pack everything together *)
Module Biorthogonality (T : TstElt).
  Module Export GC := EnsembleGC T.
  Module Export CO := GCClosure GC.
End Biorthogonality.
