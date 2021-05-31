(*begin hide*)
Require Import Utils.
Require Import Program.

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

Add LoadPath "../domain-theory".
Add LoadPath "../extended-cbn".

Require Import DomainStuff.

Require Import Rel.
Require Import Sets.

Require Import domoprs.
Require Import PredomAll.
Require Import uniirec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition RelStable (A B : cpoType) (R : A -> B -> Prop) : Prop :=
  forall (a a' : A) (b b' : B), a =-= a' -> b =-= b' -> R a b -> R a' b'.

Lemma TranspStable (A B : cpoType) (R : A -> B -> Prop) : RelStable R -> RelStable (transpose R).
Proof.
  intros A B R RS.
  intros b b' a a' eqb eqa rel.
  apply (RS _ _ _ _ eqa eqb rel).
Qed.

Definition chain_complete (D E : cpoType) (r : D -> E -> Prop) : Prop :=
  forall (chs : natO -=> D) (chs' : natO -=> E),
    (forall i, r (chs i) (chs' i)) -> r (lub chs) (lub chs').

Lemma TranspCC (A B : cpoType) (R : A -> B -> Prop) :
  chain_complete R -> chain_complete (transpose R).
Proof.
  intros A B R Rcc.
  intros chs chs' cc.
  unfold transpose.
  apply Rcc.
  apply cc.
Qed.

Definition RelFunc (D D' : cpoType) (R : D -> D' -> Prop) : Prop :=
    forall (v : D) (v' v'' : D'), R v v' -> R v v'' -> v' =-= v''.

Definition RelMono (D D' : cpoType) (R : D -> D' -> Prop) : Prop :=
    (forall (v : D) (v' v'' : D'), R v v' -> R v v'' -> v' <= v'').

Lemma FuncToMono (D D' : cpoType) (R : D -> D' -> Prop) : RelFunc R -> RelMono R.
Proof.
  intros D D' R RF.
  intros a b b' rel rel'.
  apply (RF _ _ _ rel rel').
Qed.

(** Lemmas about lifting *)
Lemma pred_Bot (X : cpoType) : forall j, pred_nth PBot j  = Eps (DL_bot X).
Proof.
  intro X.
  assert (PBot = (@Eps X (DL_bot X))).
  rewrite <- DL_bot_eq. auto.
  intros j.
  induction j.
  by simpl. 
  rewrite pred_nth_Sn_acc.
  rewrite H.
  by simpl.
Qed.
Lemma ValNotBot (X : cpoType) : forall (x : X), ~ (Val x = PBot).
Proof.
  intros X x hip.
  unfold PBot in hip; simpl in hip ; rewrite DL_bot_eq in hip.
  discriminate hip.
Qed.

Lemma pred_eps_val : forall D n x (d : D), pred_nth (Eps x) n = Val d -> exists m, pred_nth x m = Val d.
Proof.
  intros D n x d equ.
  destruct n.
  simpl in equ.
  discriminate equ.
  simpl in equ.
  by exists n.
Qed.  

Lemma pred_val_val : forall D n (d d' : D),  pred_nth (Val d) n = Val d' -> d = d'.
Proof.
  intros E n d d' H.
  destruct n.
  - simpl in H ; by inversion H.
  - simpl in H ; by inversion H.
Qed.

Lemma ValMono (D : cpoType) : forall (a b : D), a <= b -> Val a <= Val b.
Proof.
  intros E a b rel.
  eapply DLleVal with (n := 0) . 
  simpl. reflexivity.
  assumption.
Qed.

Lemma eqLubChains (D : cpoType) (ch : ordCatType natO D)
      (chs : ordCatType natO (D _BOT)) k : (forall n : nat, chs (k + n)%N =-= Val (ch n)) ->
                    (lub chs =-= Val (lub ch)).
Proof.
  intros E ch chs k eq_ch.
  split.
  apply lub_le.
  intro n. eapply Ole_trans with (y := chs (k + n)%N).
  apply fmonotonic. apply leq_addl.
  rewrite (eq_ch n).
  apply ValMono.
  apply le_lub.
  simpl.
  pose proof (chainVallubnVal 1 (eq_ch k)) as [lc eqlub].
  destruct (eqValpred eqlub) as [n [lc' [prd lceq]]] .
  eapply DLleVal with (d' := lc').
  unfold lub. simpl. unfold DL_lub. 
  apply prd.
  apply lub_le.
  intro m. 
  specialize (eq_ch m).
  destruct (eqValpred eq_ch) as [p [dp [prk dkeq]]] .
  rewrite dkeq. apply vleinj.
  eapply Ole_trans with (y := chs ((k+m)%N)).
  rewrite <- prk.
  apply pred_nth_eq.
  eapply Ole_trans with (y := lub chs).
  apply le_lub.
  unfold lub. simpl.
  eapply Ole_trans with (y := Val lc).
  apply eqlub.
  apply ValMono.
  apply lceq.
Qed.

(*end hide*)

(** *)
(*** Section 4: MEANING OF TYPES
***)
(** *)

Section StrictExt.

Variable D D' : cpoType.
Variable R : D -> D' -> Prop.

(** *Coinductive definition: Strict Extension *)
CoInductive SE : D _BOT -> D' _BOT -> Prop :=
|  SB : forall x y,  SE x y -> SE (Eps x) (Eps y)
|  SV : forall d d' n m x y, pred_nth x n = Val d -> pred_nth y m = Val d' ->
                        R d d' -> SE x y.

(** *Lemma 4.2.1: Embedding-projections pairs *)
Lemma SBotIn : SE (@DL_bot D) (@DL_bot D').
Proof.
  cofix SBotIn.
  rewrite (@DL_bot_eq D') ; rewrite (@DL_bot_eq D).
  apply SB;  apply SBotIn.
Qed.

Hint Constructors SE.
  
(* Values are not related with ⊥. *)
Lemma valNotRelBotL x d  : SE (Val d) x -> x <> (@DL_bot D').
  intros x d H Hyp.
  rewrite Hyp in H.
  inversion H.
  rewrite (pred_Bot _ m) in H1.
  discriminate H1.
Qed.

(* Only bottom is related with bottom, generalised version *)
Lemma SEBotOutGL x : (x <= @DL_bot D) -> forall y, SE x y -> y <= (@DL_bot D').
Proof.
  cofix SEBotOutGL.
  intros x leq y H.
  + inversion H as [x' y' Rel eqx eqy | d d' n m x' y' eqx eqy Rel eqx' eqy'].
    - rewrite DL_bot_eq.
      assert (leq' : x' <= @DL_bot D). apply Ole_trans with (y := x).
      rewrite <- eqx. apply eq_Eps. apply leq.
      apply DLleEps.
      apply (SEBotOutGL x' leq' y' Rel).
    - assert (eq' : x =-= eta d). apply tset_trans with (y := pred_nth x n).
      symmetry. apply pred_nth_eq. auto.
      assert (leq' : eta d <= @DL_bot D).
      apply Ole_trans with (y := x).
      apply eq'. apply leq.
      elim (PBot_incon leq').
Qed.

Corollary SEBotOutL y : SE (@DL_bot D) y -> y <= (@DL_bot D').
Proof. intros y H.
       by apply (SEBotOutGL (Ole_refl (@DL_bot D))).
Qed.

(** *Lemma 4.3.1: Embedding-projections pairs *)
Lemma SEValOutL y d  : SE (Val d) y -> exists d', y =-= Val d' /\ R d d'.
Proof.
  intros y d H.
  inversion H.
  exists d'. split. setoid_rewrite <- H1.
  symmetry. apply pred_nth_eq.
  apply pred_val_val in H0.
  by rewrite H0.
Qed.

(* *)
Lemma SEEpsR : forall x y, SE x y -> SE x (Eps y).
Proof.
  cofix SEEpsR.
  intros x y rel.
  inversion rel.
  apply SB.
  by apply SEEpsR.
  eapply SV with (n := n) (m := S m).
  apply H. simpl. apply H0.
  assumption.
Qed.

Lemma SEPredEpsL : forall x y, SE (Eps x) y -> SE x y.
Proof.
  intros x y rel.
  apply SEEpsR in rel.
  inversion rel.
  apply H1.
  apply pred_eps_val in H as [k equ].
  apply pred_eps_val in H0 as [k' equ'].
  eapply SV. apply equ. apply equ'. apply H1.
Qed.

Lemma SEPredL : forall x y, SE x y -> SE (pred x) y.
Proof.
  intros x y rel.
  destruct x.
  simpl. by apply SEPredEpsL.
  by simpl.
Qed.

Lemma SEPrednthL x y  : SE x y -> forall n, SE (pred_nth x n) y.
Proof.
  intros x y  rel n.
  induction n.
  by simpl.
  rewrite pred_nth_Sn.
  by apply SEPredL.
Qed.

Lemma SEValStable d d' (rel : R d d') x y  :
  RelStable R ->
  x =-= Val d -> y =-= Val d' -> SE x y.
Proof.
  intros d d' rel x y R_stable eqx eqy.
  destruct (eqValpred eqy) as [n [e [eqa eqb]]].
  destruct (eqValpred eqx) as [m [e' [eqc eqd]]].
  eapply (SV eqc eqa). apply (R_stable _ _ _ _  eqd eqb rel).
Qed.

End StrictExt.

Lemma SESym (D D' : cpoType) (R : D -> D' -> Prop) x y :
  SE R x y -> SE (transpose R) y x.
Proof.
  move => D D' R. cofix SESym.
  move => x y rel.
  inversion rel.
  apply SB.
  by apply SESym.
  eapply SV. apply H0. by apply H.
  by simpl.
Qed.

Section StrictExtR.
Variable D D' : cpoType.
Variable R : D -> D' -> Prop.

Lemma valNotRelBotR   (x : D _BOT) (d : D')  :
  SE R x (Val d) -> x <> (@DL_bot D).
Proof.
  intros x d rel eq.
  apply (@valNotRelBotL _ _ (transpose R)  x d (SESym rel) eq).
Qed.

(** *Lemma 4.3.2: Embedding-projections pairs *)
Lemma SEValOutR x d' : SE R x (Val d') -> exists d, x =-= Val d /\ R d d'.
Proof.
  intros x d' rel.
  apply (@SEValOutL _ _ (transpose R)  x d' (SESym rel)).
Qed.

Lemma SEEpsL : forall x y, SE R x y -> SE R (Eps x) y.
Proof.
  intros x y rel.
  apply (SESym ((@SEEpsR _ _ (transpose R) _ _ (SESym rel)))). 
Qed. 

Lemma SEPredEpsR : forall x y, SE R x (Eps y) -> SE R x y.
Proof.
  intros x y rel.
  apply (SESym ((@SEPredEpsL _ _ (transpose R) _ _ (SESym rel)))). 
Qed.

Lemma SEPredR : forall x y, SE R x y -> SE R x (pred y).
Proof.
  intros x y rel.
  apply (SESym ((@SEPredL _ _ (transpose R) _ _ (SESym rel)))). 
Qed.

Lemma SEPrednthR x y  : SE R x y -> forall n, SE R x (pred_nth y n).
Proof.
  intros x y rel n.
  apply (SESym ((@SEPrednthL _ _ (transpose R) _ _ (SESym rel) n))). 
Qed.

End StrictExtR.  

Lemma SEStableR (D D' : cpoType) (R : D -> D' -> Prop)
  : RelStable R ->
    forall (x : D _BOT) (y : D' _BOT),
      SE R x y -> forall w, y =-= w -> SE R x w.
Proof.
  intros D D' R R_stable. cofix SEStableR.
  intros x y rel w eqy.
  inversion rel.
  destruct w.
  assert (eq' : y0 =-= w).
  apply tset_trans with (y := y).
  rewrite <- H1. apply eq_Eps. by rewrite (eq_Eps w).
  apply SB.
  eapply (SEStableR x0 y0 H w eq').
  rewrite <- H1 in eqy.
  pose proof (eqValpred  eqy) as [n [d [eq eq']]].
  destruct n.
  discriminate eq.
  pose proof (SEPrednthR H n) as srel'.
  simpl in eq.
  rewrite eq in srel'.
  apply SEEpsL.
  pose proof (SEValOutR srel') as [de [equ rel' ]].
  apply (SEValStable rel' R_stable  equ (eqDLeq eq')).
  apply (SEValStable  H1 R_stable). auto.
  rewrite <- H. by rewrite pred_nth_eq.
  rewrite <- eqy. rewrite <- H0. by rewrite pred_nth_eq.
Qed.

Lemma SEStableL (D D' : cpoType) (R : D -> D' -> Prop)
  : RelStable R ->
    forall (x : D _BOT) (y : D' _BOT),
      SE R x y -> forall w, x =-= w -> SE R w y.
Proof.
  intros D D' R R_stable x y rel w eq.
  apply (SESym ((SEStableR (TranspStable R_stable) (SESym rel) eq))).
 Qed.
  
Lemma SEStable (D D' : cpoType) (R : D -> D' -> Prop)
  : RelStable R -> RelStable (SE R).
Proof.
  intros D D' R R_stable x x' y y' rel eqx eqy.
  apply (SEStableR R_stable (SEStableL R_stable eqy rel) eqx).
Qed.

Lemma SEChainCompleteVal (D D' : cpoType) (R : D -> D' -> Prop) :
  RelStable R ->
  chain_complete R ->
  forall (chs : natO -=> D _BOT) (chs' : natO -=> D' _BOT) x v,
    lub chs =-= x -> lub chs' =-= Val v -> 
    (forall i, SE R (chs i) (chs' i)) -> SE R x  (Val v).
Proof.
  intros D D' R RS H.
  intros chs chs' x v  eq eq' cc.
  destruct (lubval eq') as [k' [d' [eqv' leq']]].
    assert (cc' := cc).
    specialize (cc k'). eapply (SEStableR RS ) in cc. 2 : { apply eqv'. }
    destruct (SEValOutR cc) as [d [eqv leq]].
    pose proof (DLvalgetchain eqv) as [ch eq_ch].
    pose proof (DLvalgetchain eqv') as [ch' eq_ch'].
    assert (allRel : forall i, R (ch i) (ch' i)).
    intro i.
    specialize (cc' (k' + i)%N).
    apply (SEStableL RS) with (w := Val (ch i)) in cc'.
    destruct (SEValOutL  cc') as [v' [eqn' rel]].
    specialize (eq_ch' i).
    rewrite eq_ch' in eqn' *. intro eqn'. pose proof (vinj eqn') as eqn''.
    apply (RS _ _ _ _  (tset_refl (ch i)) (tset_sym eqn'') rel).
    apply (eq_ch i).
    pose proof (H _ _ allRel) as lubRel.
    pose proof (eqLubChains  eq_ch).
    pose proof (eqLubChains  eq_ch').
    clear cc cc' allRel eq_ch eq_ch' eqv eqv' leq leq' k' d d'.
    destruct (eqValpred H0) as [k [d [eql eql1]]].
    eapply (SEStableL RS) with (x := lub chs).
    eapply SV with (d := d) (m := 0).
    apply eql.
    by simpl.
    eapply RS .
    apply eql1.
    setoid_rewrite eq' in H1 .
    apply vinj.
    apply (tset_sym H1).
    apply lubRel.
    assumption.
Qed.

Lemma TranspSE (D D' : cpoType) (R : D -> D' -> Prop) :
  forall x y, SE R x y -> SE (transpose R) y x.
Proof.
  intros D D' R. cofix TranspSE.
  intros x y rel.
  destruct rel as [rel' | d d' n m  x y eq eq' rel'].
  apply SB; by apply TranspSE.
  eapply SV. apply eq'. apply eq.
  assumption.
Qed.

Lemma SEChainCompleteG (D D' : cpoType) (R : D -> D' -> Prop) :
  RelStable R ->
  chain_complete R ->
  forall (chs : natO -=> D _BOT) (chs' : natO -=> D' _BOT),
    (forall i, SE R (chs i) (chs' i)) -> forall w w',
      lub chs =-= w -> lub chs' =-= w' -> 
      SE R w w'.
Proof.
  intros D D' R RS H.
  cofix SEChainCompleteG.
  intros chs chs' cc w w' eq eq'.
  destruct w  as [x | s].
  destruct w' as [y | s'] .
  apply SB.
  apply (SEChainCompleteG chs chs' cc).
  rewrite -> eq;  apply (tset_sym (eq_Eps x)).
  rewrite -> eq'; apply (tset_sym (eq_Eps y)).
  clear SEChainCompleteG.
  - apply (SEChainCompleteVal RS H eq eq' cc).
  - apply SESym.
    apply (SEChainCompleteVal (TranspStable RS) (TranspCC H) eq' eq).
    intro i ; apply (TranspSE (cc i)).
Qed.

(** *Lemma 4.5.2: Embedding-projections pairs *)
Corollary SEChainComplete (D D' : cpoType) (R : D -> D' -> Prop) : 
  RelStable R ->
  chain_complete R -> chain_complete (SE R).
Proof.
  intros D D' R RS ccR chs chs' allRel.
  apply (SEChainCompleteG RS ccR allRel (tset_refl (lub chs)) (tset_refl (lub chs'))).
Qed.

Lemma SEFuncVal : forall (D D' : cpoType) (R : D -> D' -> Prop), RelFunc R ->
    (forall (d : D) (d' d'' : D' _BOT),
        SE R (Val d) d' -> SE R (Val d) d'' -> d' =-= d'').
Proof.
  intros D D' R RF d d' d'' rel rel'.
  destruct (SEValOutL rel) as [? [? ?]].
  destruct (SEValOutL rel') as [? [? ?]].
  rewrite H H1.
  apply Val_eq_compat.
  by apply RF with (v:=d).
Qed.

Lemma SEMonEps : forall (D D' : cpoType) (R : D -> D' -> Prop),
    RelStable R ->
    RelMono R -> 
    (forall (d : D _BOT) (d' d'' : D' _BOT),
        SE R (Eps d) d' -> SE R (Eps d) d'' -> d' <= d'').
Proof.
  intros D D' R RS RM.
  cofix SEMonEps.
  intros d d' d'' rel rel'.
  destruct d'. destruct d''.
  apply DLleEps.
  eapply SEMonEps. 
  apply SEPredR in rel. apply rel.
  apply SEPredR in rel'. apply rel'.
  apply DLleEpsVal.
  eapply SEMonEps. 
  apply SEPredR in rel; apply rel.
  apply rel'.
  destruct (SEValOutR rel) as [e [eqe rele]].
  apply (SEStableL RS) with (w:=Val e) in rel'.
  destruct (SEValOutL rel') as [e' [eqe' rele']].
  rewrite eqe'. apply Val_le_compat.
  apply (RM _ _ _ rele rele'). 
  assumption.
Qed.

Lemma SEFuncEps : forall (D D' : cpoType) (R : D -> D' -> Prop),
    RelStable R ->
    RelFunc R ->
    (forall (d : D _BOT) (d' d'' : D' _BOT),
        SE R (Eps d) d'' -> SE R (Eps d) d' -> d' =-= d'').
Proof.
  intros D D' R RS RF d d' d'' rel rel'.
  split.
  apply (SEMonEps RS (FuncToMono RF) rel' rel).
  apply (SEMonEps RS (FuncToMono RF) rel rel').
Qed.

Lemma SEFunc (D D' : cpoType) (R : D -> D' -> Prop) : 
  RelStable R -> RelFunc R -> RelFunc (SE R).
Proof.
  intros D D' R RS RF d d' d'' rel rel'.
  destruct d. 
  apply (@SEFuncEps _ _ R RS RF d d' d'' rel' rel). 
  apply (SEFuncVal RF rel rel').
Qed.
