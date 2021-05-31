(** * Sequences : Formalization of finite and infinite sequences *)
(* This file is a modification of 
http://pauillac.inria.fr/~xleroy/courses/Marktoberdorf-2009/  *)
Require Omega.
Set Implicit Arguments.

Section SEQUENCES.

  Variable A: Type.
  Variable R: A -> A -> Prop.

(** Zero, one or several transitions: reflexive, transitive closure of [R]. *)

  Inductive star: A -> A -> Prop :=
  | star_refl: forall a,
    star a a
  | star_step: forall a b c,
    R a b -> star b c -> star a c.

  Lemma star_ind':
    forall (P : A -> A -> Prop),
      (forall a, P a a) ->
      (forall a b c, R a b -> star b c -> P b c -> P a c) ->
      (forall a b, star a b -> P a b).
  Proof.
    intros P Q0 Q1.
    induction 1.
    eapply Q0.
    eapply Q1 ; eauto.
  Qed.

  Lemma star_one:
    forall (a b: A), R a b -> star a b.
  Proof.
    intros. econstructor; eauto. constructor.
  Qed.

  Lemma star_trans:
    forall (a b: A), star a b -> forall c, star b c -> star a c.
  Proof.
    induction 1; intros. auto. econstructor; eauto.
  Qed.

  (** One or several transitions: transitive closure of [R]. *)

  Inductive plus: A -> A -> Prop :=
  | plus_left: forall a b c,
    R a b -> star b c -> plus a c.

  Lemma plus_one:
    forall a b, R a b -> plus a b.
  Proof.
    intros. apply plus_left with b. auto. apply star_refl.
  Qed.

  Lemma plus_star:
    forall a b, plus a b -> star a b.
  Proof.
    intros a b Pab.
    inversion Pab.
    subst.
    eapply star_step ;
    eauto.
  Qed.

  Lemma plus_step:
    forall a b c, R a b -> plus b c -> plus a c.
  Proof.
    intros a b c Rab Pbc.
    econstructor.
    eauto.
    eapply plus_star.
    auto.
  Qed.

  Lemma plus_star_plus:
    forall a b c, star a b -> plus b c -> plus a c.
  Proof.
    induction 1 ;
    intros ;
    eauto.
    eapply plus_step ;
    auto.
    auto.
  Qed.

  Lemma plus_trans:
    forall a b c, plus a b -> plus b c -> plus a c.
  Proof.
    intros.
    inversion H0.
    subst. inversion H. subst.
    assert(star b1 c).
    assert(star b c).
    eapply star_step.
    eexact H1. auto.
    eapply star_trans. eauto. auto.
    eapply plus_left. eauto. auto.
  Qed.

  (** More definitions *)

  Definition blocked (a : A) := forall b, ~ R a b.
   
  Definition deterministic := 
    forall a b, R a b -> forall b', R a b' -> b = b'.  

  (** Numbered transitions *)

  Inductive count :  nat -> A -> Prop :=
  | zero : forall a, count 0 a 
  | step : forall a b n, count n b -> R a b -> count (S n) a.

  Lemma count_succ:
    forall n a, count (S n) a -> count n a.
  Proof.
    induction n.
    intros a Q. 
    constructor.
    intros a Q.
    inversion Q.
    subst.
    econstructor.
    eapply IHn ;
    eauto. eauto.
  Qed.

  Lemma count_inv:
    forall n a b, deterministic -> count (S n) a -> R a b -> count n b.
  Proof.
    intros n a b det count rab.
    inversion count as [ | a' c m count' rac].
    subst.
    set (Q := det _ _ rab _ rac).
    rewrite Q.
    auto.
  Qed.
                    
  (** Infinitely many transitions. *)
  
  CoInductive infseq: A -> Prop :=
  | infseq_step: forall a b,
    R a b -> infseq b -> infseq a.

  Lemma blocked_unique:
    deterministic ->
    forall a b,
      star a b -> 
      blocked b ->
      forall c,
        star a c ->
        blocked c -> 
        b = c.
  Proof.
    intro det.
    set (P a b := blocked b -> forall c, star a c -> blocked c -> b = c).
    intros a b Q.
    fold (P a b).
    generalize a b Q.
    clear Q a b.
    eapply star_ind ;
    unfold P in * ;
    clear P.
    intros a ba c s0 bc.
    destruct s0 as [? | a0 a1 a2 R0].
    auto.
    contradict R0.
    eapply ba.
    intros a b c R0 s0 Hip1 bc.
    specialize (Hip1 bc).
    intros a0 s1 ba0.
    destruct s1 as [? | a0 a1 a2 R1].
    contradict R0.
    eapply ba0.
    assert (b = a1).
    unfold deterministic in det.
    eapply det ; eauto.
    subst.
    eapply Hip1 ;
    eauto.
  Qed.

End SEQUENCES.
















