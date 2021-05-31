(****
   Auxiliary facts about the denotational semantics for
   Biorthogonality, Step-Indexing & Compiler Correctness
   Nick Benton & Chung-Kil Hur
   April 2009
 ****)

Add LoadPath "../domain-theory".
Set Automatic Coercions Import.
Unset Automatic Introduction.
(* endof new in 8.4 *)

Require Import PredomAll.
Set Implicit Arguments.
Unset Strict Implicit.

Definition prdc (A:Type) := A->Prop.
Definition sub (A : Type) (p q : prdc A) := forall a, p a -> q a.
Definition sub2 (A B: Type) (p q : A -> B -> Prop) := forall a b, p a b -> q a b.
Definition sub3 (A B C: Type) (p q : A -> B -> C -> Prop) := forall a b c, p a b c -> q a b c.
Definition union (A : Type) (p q : prdc A) : prdc A := fun a => p a \/ q a.
Definition intersection (A:Type) (p q : prdc A) : prdc A := fun a => p a /\ q a.

Lemma sub_trans: forall (A:Type) (P Q R:prdc A), sub P Q -> sub Q R -> sub P R.
intros.
red.
intros.
apply H0.
apply H.
assumption.
Qed.


(****
   General Lemmas
 ****)
(* Section General_Lemmas. *)

Lemma le_simple_ind: forall (P:nat->Prop), (forall k, P (S k) -> P k) ->
                                  (forall k k', (k <= k')%coq_nat -> P k' -> P k).
  move => P hip k k' leq Pk'; move: leq.
  elim (leP (m:=k) (n:=k')).
  move => leq p; clear p.
  induction leq.  
  - by [].
  - apply IHleq; by apply hip.
    move => nleq Abs. apply nleq in Abs.
    inversion Abs.
Qed.

(****
   Domain Operations
****)
(* Section Domain_Operations. *)


Definition chain_closed (D:cpoType) (P:prdc D) : Prop :=
  forall chs: natO-=>D, (forall i, P (chs i)) -> P (lub chs).

Definition down_closed (D:cpoType) (P: prdc D) : Prop :=
  forall d d', (d <= d') -> P d' -> P d.

Definition closed (D:cpoType) (P:prdc D) := chain_closed P /\ down_closed P.

Definition ideal_closure (D:cpoType) (P:prdc D) : prdc D := fun d =>
  forall (S: prdc D), sub P S -> chain_closed S -> down_closed S -> S d.

Lemma ideal_closure_covar: forall (D:cpoType) (P P':prdc D),
  sub P P' -> sub (ideal_closure P) (ideal_closure P'). 
do 2 red; intros. apply H0.
eapply sub_trans. apply H. apply H1. auto. auto.
Qed.

Lemma ideal_closure_closed: forall (D:cpoType) (P:prdc D),
  closed (ideal_closure P).
intros. split.
do 2 red; intros.
apply H1. intros. apply H. auto. auto. auto.

do 2 red; intros.
apply H3 with d'. auto.
apply H0. auto. auto. auto.
Qed.

Lemma ideal_closure_sub: forall (D:cpoType) (P:prdc D),
  sub P (ideal_closure P).
do 2 red; intros. apply H0. auto.
Qed.

Lemma IntroVar_lem: forall (A:Type) (x:A), exists y, y = x.
intros. exists x. auto.
Qed.
Implicit Arguments IntroVar_lem [A].

Ltac introvar var term Hname := assert (Hname := IntroVar_lem term); destruct Hname as [var Hname].

Lemma DLvalval2 : forall (D:cpoType) (d:D) x, DLle (Val d) x -> 
 exists d', x =-= Val d' /\ (d<=d').
intros D d x H.
destruct (DLvalval H).
do 2 destruct H0.
exists x1.
split.
apply Oeq_sym.
apply Val_exists_pred_eq.
exists x0; auto.
auto.
Qed.

Lemma DL_bot_neq: forall (D:cpoType) (d:D), ~ (Val d <= DL_bot D).
red; intros.
destruct (DLvalval H).
do 2 destruct H0.
induction x.
simpl in H0.
rewrite DL_bot_eq in H0.
inversion H0.
rewrite DL_bot_eq in H0.
simpl in H0.
apply IHx.
assumption.
Qed.

Lemma DLleVal_eq2 :
  forall (D:cpoType) (d d':D), Val d =-= Val d' -> d =-= d'.

intros.
destruct H.
split.
apply DLleVal_leq; auto.
apply DLleVal_leq; auto.
Qed.

Lemma Val_stable: forall (D:cpoType), stable (@Val D).
red; intros.
split. simpl. apply DLle_leVal. apply H.
simpl. apply DLle_leVal. apply H.
Qed.

Lemma DL_lub_val: forall (D:cpoType) (f:natO-=>  D _BOT) (d:D) , 
  (Val d <= DL_lub f) -> exists k, exists d', f k =-= Val d'.

intros.
destruct (@DLnvalval _ 0 (Val d) d (DL_lub f)).
auto. assumption.
do 2 destruct H0.
unfold DL_lub in H0.
destruct (attempt2 H0).
do 2 destruct H2.
exists x1.
exists x2.
assumption.
Qed.

Lemma ideal_closure_flat: forall (T : Type)
                            (P: prdc ((discrete_cpoType T) _BOT))
                            (d : T),
    (forall p q, p =-= q -> P p -> P q) -> ideal_closure P (Val d) -> P (Val d).
Proof.
  intros T P d H H0.
  introvar P'
           (fun (x: (discrete_cpoType T) _BOT) =>  (exists x', x =-= Val x') -> P x)
           HP'.
  assert (P' (Val d)).
  - (* Case "Assert". *)
    apply H0.
    + (* SCase "P ⊆ P'". *)
      red; intros. rewrite HP'. intros. auto.
    + (* SCase "P' Chain closed". *)
      rewrite HP'. red; intros. destruct H2.
      destruct (lubval H2) as [i [x' [? ?]]]. simpl in H4. rewrite <- H4 in H2.
      eapply H. eapply Oeq_trans. apply H3. apply (Oeq_sym H2).
      apply H1. exists x'. auto.
    + (* SCase "P' Down closed". *)
      rewrite HP'. red; intros. destruct H3 as [x' H3].
      setoid_rewrite H3 in H1.
      destruct (DLvalval2 H1) as [? [? ?]]. simpl in H5. rewrite <- H5 in *.
      eapply H. eapply Oeq_trans. apply H4. apply (Oeq_sym H3).
      apply H2. exists x'.  auto.
  rewrite HP' in H1. apply H1. exists d. auto.
Qed.

(*
   chain2
 *)

Definition chain2 (A B : cpoType) (ca : natO =-> A) (cb : natO =-> B) :
  natO =-> (A * B) := Prod_fun ca cb.

Lemma chain2_lub_simpl : forall (A B C : cpoType)
                           (f : (A * B) =-> C)
                           (cp : natO =-> (A * B)),
    f (lub cp) =-= f (lub (Fst A B << cp), lub (Snd A B << cp)).
Proof.
  intros A B C f cp. by simpl.
Qed.

Lemma chain2_eval: forall A B ca cb n, @chain2 A B ca cb n =-= (ca n, cb n).
Proof.
  intros A B ca cb n. by simpl.
Qed.

Lemma chain2_fst : forall (A B : cpoType) ca cb, Fst A B << (chain2 ca cb) =-= ca.
Proof.
  intros A B ca cb. auto.
Qed.

Lemma chain2_snd : forall (A B : cpoType) ca cb, Snd A B << (chain2 ca cb) =-= cb.
Proof.
  intros A B ca cb. auto.
Qed.

Definition chain2_fun (A B C : cpoType)
           (f : A =-> (B -=> C)) (ca : natO =-> A) (cb : natO =-> B)
  : natO =-> C
  := ocomp (uncurry f) (chain2 ca cb).

Lemma chain2_fun_simpl : forall (A B C : cpoType) (f : A =-> (B -=> C))
                           (ca : natO =-> A) (cb : natO =-> B) (n : natO),
    chain2_fun f ca cb n =-= f (ca n) (cb n).
Proof.
  intros A B C f ca cb n. by simpl.
Qed.

Lemma chain2_fun_lub : forall (A B C : cpoType) (f : A =-> (B -=> C))
                         (ca : natO =-> A) (cb : natO =-> B),
    lub (chain2_fun f ca cb) =-= f (lub ca) (lub cb).
Proof.
  intros A B C f ca cb.
  assert (f (lub ca) (lub cb) =-= uncurry f (lub ca, lub cb)) by (by simpl).
  rewrite H.
  unfold chain2_fun.
  rewrite <- lub_comp_eq. rewrite chain2_lub_simpl.
  rewrite chain2_fst. by rewrite chain2_snd.
Qed.

(*
   chain3
*)

Definition chain3 (A B C: cpoType)
           (ca : natO =-> A)
           (cb : natO =-> B)
           (cc : natO =-> C) : natO =-> A * B * C
  := Prod_fun (Prod_fun ca cb) cc.

Lemma chain3_lub_simpl: forall (A B C D : cpoType)
                          (f  : (A * B * C) =-> D)
                          (cp : natO =-> (A * B * C)),
    f (lub cp) =-= f ((lub (Fst A B << Fst (A * B) C << cp),
                       lub (Snd A B << Fst (A * B) C << cp)),
                       lub (Snd (A * B) C << cp)
                     ).
Proof.
  intros.
  rewrite chain2_lub_simpl.
  apply fmon_eq_compat. apply tset_refl.
  apply pair_eq_compat.
  split.
  simpl.
  split.
  apply lub_le_compat. rewrite comp_assoc. unfold pi1. simpl. auto.
  apply lub_le_compat. rewrite comp_assoc. unfold pi2. simpl. auto.
  split.
  apply lub_le_compat. rewrite comp_assoc. unfold pi1. simpl. auto.
  apply lub_le_compat. rewrite comp_assoc. unfold pi2. simpl. auto.
  apply lub_eq_compat. auto.
Qed.

Lemma chain3_fst : forall (A B C: cpoType)
                     (ca : natO =-> A)
                     (cb : natO =-> B)
                     (cc : natO =-> C),
    Fst _ _ << Fst _ _ << (@chain3 A B C ca cb cc) =-= ca.
Proof.
  intros A B C ca cb cc.
  auto.
Qed.

Lemma chain3_snd : forall (A B C: cpoType)
                     (ca : natO =-> A)
                     (cb : natO =-> B)
                     (cc : natO =-> C),
    Snd _ _ << Fst _ _ << (@chain3 A B C ca cb cc) =-= cb.
Proof.
  intros A B C ca cb cc.
  auto.
Qed.

Lemma chain3_third : forall (A B C: cpoType)
                     (ca : natO =-> A)
                     (cb : natO =-> B)
                     (cc : natO =-> C),
    Snd _ _ << (@chain3 A B C ca cb cc) =-= cc.
Proof.
  intros A B C ca cb cc.
  auto.
Qed.

Definition chain3_fun (A B C D: cpoType)
           (f : A =-> (B -=> (C -=> D))) 
           (ca : natO =-> A) (cb : natO =-> B) (cc : natO =-> C)
  : natO =-> D :=
  ocomp (uncurry (uncurry f)) (chain3 ca cb cc).

Lemma chain3_fun_simpl : forall (A B C D: cpoType)
                           (f : A =-> (B -=> (C -=> D))) 
                           (ca : natO =-> A) (cb : natO =-> B) (cc : natO =-> C)
                           (n : natO),
    chain3_fun f ca cb cc n =-= f (ca n) (cb n) (cc n).
Proof.
  intros A B C D f ca cb cc n. auto.
Qed.

Lemma chain3_fun_lub : forall (A B C D: cpoType)
                         (f : A =-> (B -=> (C -=> D))) 
                         (ca : natO =-> A) (cb : natO =-> B) (cc : natO =-> C),
    lub (@chain3_fun A B C D f ca cb cc) =-= f (lub ca) (lub cb) (lub cc).
Proof.
  intros A B C D f ca cb cc.
  setoid_replace (f (lub ca) (lub cb) (lub cc))
  with (uncurry (uncurry f) ((lub ca, lub cb), lub cc)).
  unfold chain3_fun.
  rewrite <- lub_comp_eq.
  rewrite chain3_lub_simpl.
  apply fcont_eq_compat.
  apply tset_refl.
  rewrite chain3_fst.
  rewrite chain3_snd.
  rewrite chain3_third.
  apply tset_refl.
  auto.
Qed.

(*
   continuous closed
*)
Lemma cont_closed: forall (D1 C : cpoType) (f:D1 =-> C) (P: prdc D1) (S: prdc C),
  closed S -> (forall p, P p -> S (f p)) ->
  forall p, ideal_closure P p -> S (f p).

intros. apply H1. 
  red; intros. apply H0. auto.

  red; intros. eapply H. apply (lub_comp_eq f chs).
  apply H. intros. eapply H. simpl. apply Ole_refl. apply H2.

  red; intros. eapply H. rewrite H2. apply Ole_refl. auto.
Qed.

Lemma cont2_closed: forall (D1 D2 D3 : cpoType)
                      (f : D1 =-> (D2 -=> D3))
                      (P: prdc D1) (Q: prdc D2)
                      (S: prdc D3),
  closed S -> (forall p q, P p -> Q q -> S (f p q)) ->
  forall p q, ideal_closure P p -> ideal_closure Q q -> S (f p q).
Proof.
  intros D1 D2 D3 f P Q S H H0 p q H1 H2.
  intros. generalize q H2; clear H2 q. apply H1.
  - (* Case "P ⊆ ...". *)
    red; intros. apply H3.
    + (* SCase "Q ⊆ ...". *)
      red; intros. eapply H0. auto. auto.
    + (* SCase "chain_closed". *)
      red; intros. eapply H. erewrite <- (lub_const a).
      apply (chain2_fun_lub f _ _).
      apply H. intros. eapply H. simpl. apply Ole_refl. apply H4.
    + (* SCase "down_closed". *)
      red; intros. eapply H. rewrite H4. apply Ole_refl. auto.
  - (* Case "chain_closed". *)
    red; intros. eapply H. rewrite <- (lub_const q).
    apply (chain2_fun_lub f _ _).
    apply H. intros. eapply H. simpl. apply Ole_refl. apply H2. auto.
  - (* Case "down_closed". *)
    red; intros. eapply H. rewrite H2. apply Ole_refl. auto.
Qed.

Lemma cont3_closed: forall (D1 D2 D3 D4 : cpoType)
                      (f : D1 =-> (D2 -=> (D3 -=> D4)))
                      (P: prdc D1) (Q: prdc D2) (R: prdc D3)
                      (S: prdc D4),
  closed S -> (forall p q r, P p -> Q q -> R r -> S (f p q r)) ->
  forall p q r, ideal_closure P p -> ideal_closure Q q -> ideal_closure R r ->
           S (f p q r).
Proof.
  intros D1 D2 D3 D4 f P Q R S H H0 p q r H1 H2 H3.
  generalize q H2 r H3; clear H3 r H2 q. apply H1.
  red; intros. generalize r H4; clear H4 r. apply H3. 
    red; intros. apply H5.
      red; intros. eapply H0. auto. auto. auto.

      red; intros. eapply H. rewrite <- (lub_const a), <- (lub_const a0).
      apply (chain3_fun_lub f _ _ _).
      apply H. intros. eapply H. simpl. apply Ole_refl. apply H6.

      red; intros. eapply H. rewrite H6. apply Ole_refl. auto.

    red; intros. eapply H. rewrite <- (lub_const a), <- (lub_const r). 
    apply (chain3_fun_lub f _ _ _).
    apply H. intros. eapply H. simpl. apply Ole_refl. apply H4. auto.

    red; intros. eapply H. rewrite H4. apply Ole_refl. auto.

  red; intros. eapply H. rewrite <- (lub_const q), <- (lub_const r). 
  apply (chain3_fun_lub f _ _ _).
  apply H. intros. eapply H. simpl. apply Ole_refl. apply H2. auto. auto.

  red; intros. eapply H. rewrite H2. apply Ole_refl. auto.
Qed.

Definition AppCpoSet
           (A B : cpoType)
           (P : prdc (A =-> B)) (P' : prdc A) : prdc B :=
  fun b => exists ab, exists a, P ab /\ P' a /\ b =-= ab a.

Lemma fcont_app_Continuous: forall (O : ordType) (D1 D2 : cpoType)
                              (f : O =-> (D1 -=> D2))
                              (h : natO =-> D1),
    fcont_app f (lub h) =-= lub (ocomp (fmon_fcont_shift f) h).
Proof.
  intros.
  split.
  - (* Case "<=". *)
    apply fcont_app_continuous.
  - (* Case ">=". *)
    simpl; intros x.
    apply lub_le; intros n; simpl.
    apply fmon_le_compat.
    apply fmon_less_preorder.
    apply le_lub.
Qed.

Lemma lub_comp_simpl: forall (A B : cpoType)
                        (f : natO -=> (fcont_cpoType A B))
                        (g: natO =-> A),
    lub f (lub g) =-= lub (fmon_diag (ocomp (fmon_fcont_shift f) g)).
Proof.
  intros.
  rewrite fcont_lub_simpl.
  rewrite fcont_app_Continuous.
  rewrite lub_diag.
  apply lub_eq_compat.
  auto.
Qed.

Lemma AppCpoSet_closed: forall (A B : cpoType) (P : prdc (A =-> B)) (P': prdc A),
    sub (AppCpoSet (ideal_closure P) (ideal_closure P'))
        (ideal_closure (AppCpoSet P P')).
Proof.
  red; intros. destruct H as [c [e [? [? ?]]]].
  eapply ideal_closure_closed. apply H1. clear H1 a.
  generalize e H0. clear H0 e. apply H.
  - (* Case "P ⊆ ...". *)
    red; intros. apply H1.
    + (* SCase "P ⊆ ...". *)
      red; intros. apply ideal_closure_sub. exists a. exists a0. auto.
    + (* SCase "Chain closed". *)
      red; intros. eapply ideal_closure_closed.
      apply (@lub_comp_eq _ _ _ _).
      apply (ideal_closure_closed _).
      intros. simpl.
      eapply ideal_closure_closed. apply Ole_refl. apply H2.
    + (* SCase "Down closed". *)  
      red; intros. eapply ideal_closure_closed. apply fmonotonic. apply H2.
      eapply ideal_closure_closed. apply Ole_refl. auto.
  - (* Case "Chain closed". *)
    red; intros. eapply ideal_closure_closed.
    rewrite <- (lub_const e).
    apply Oeq_le.
    apply lub_comp_simpl.
    apply (ideal_closure_closed _). intros. 
    eapply ideal_closure_closed. simpl. 
    apply Ole_refl. apply H0. auto.
  - (* Case "Down closed". *)
    red; intros. eapply ideal_closure_closed.
    rewrite H0. apply Ole_refl. apply H1. auto.
Qed.
