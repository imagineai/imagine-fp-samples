(*begin hide*)
Add LoadPath "../domain-theory".

Require Import Utils.
Require Import Program.

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

Require Import DomainStuff.
Require Import Lang.
Require Import Types.

Require Import PredomAll.
Require Import uniirec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.
(*end hide*)

(** *)
(*** Chapter 4: Extended Language Semantics ***)
(** *)

(** *Auxiliar typed functions *)

Definition GenBinOpTy (A B : Type) (C E : cpoType) (op : A -> B -> C) :
  (E -=> discrete_cpoType A _BOT) -=> (E -=> discrete_cpoType B _BOT) -=>
  (E -=> C _BOT)
    := exp_fun (exp_fun (
                   kleisli (eta << SimpleBOp op) << uncurry (Smash _ _)
                           << ev >< ev
                           << <| pi1 >< pi1, pi2 >< pi2|> << Id >< <| Id, Id |>
                 )
              ).
Arguments GenBinOpTy [A B C E] _.

Definition LetTy (A B C: cpoType)
  : ((A * B) -=> C _BOT) -=> (A -=> B _BOT) -=>
    (A -=> C _BOT)
  := exp_fun (exp_fun (
    ev
    <<
    KLEISLI >< (@LStrength A B)
    <<
    Id >< (Id >< ev)
    <<
    <|pi1 << pi1 , <| pi2 , <| pi2 << pi1, pi2 |> |> |>)).
Arguments LetTy [A B C].

Definition AppTy (A B C: cpoType)
  : (A -=> B -=> C _BOT) -=> (A -=> B) -=>
    (A -=> C _BOT)
  := exp_fun (exp_fun (
    ev
    <<
    ev >< ev
    <<
    <| <|pi1 << pi1, pi2|> , <| pi2 << pi1, pi2|> |>)).
Arguments AppTy [A B C].

Definition IfBTy (A B : cpoType) :
  (A -=> bool_cpoType _BOT) -=> (A -=> B _BOT) -=> (A -=> B _BOT) -=> A -=>
                 B _BOT
  := exp_fun (exp_fun (exp_fun (
  kleisli ev
  <<
  (RStrength _ _)
  <<
  kleisli (eta << IfB _ _) >< Id
  <<
  (LStrength _ _) >< Id
  <<  
  Id >< ev >< Id
  <<
  <| <| <| pi2 << pi1 << pi1, pi2 << pi1 |>
      , <| pi1 << pi1 << pi1 , pi2 |>
      |>
   , pi2
   |>
  ))).
Arguments IfBTy [A B].

Definition PairTy (A B C : cpoType) :
  (A -=> B) -=> (A -=> C) -=> (A -=> (B * C))
  := exp_fun (exp_fun (ev >< ev
                         <<
                         <|<|pi1 << pi1 , pi2|> , <|pi2 << pi1, pi2|>|>)).
Arguments PairTy [A B C].

Definition FstTy (A B C : cpoType) :
  (A -=> B * C) -=> (A -=> B _BOT)
  := exp_fun (eta << pi1 << ev).
Arguments FstTy [A B C].

Definition SndTy (A B C : cpoType) :
  (A -=> B * C) -=> (A -=> C _BOT)
  := exp_fun (eta << pi2 << ev).
Arguments SndTy [A B C].


(** *Notation *)
Reserved Notation "'t???' tjv '???v'" (at level 1, no associativity).
Reserved Notation "'t???' tje '???e'" (at level 1, no associativity).

Definition FixF (E : Env) (?? : LCtx E) (?? ??' : LType) :
  ((SemCtx (??' ?? (??' ??? ??) ?? ??)) -=> SemType ?? _BOT)
    =->
    (SemCtx ?? -=> (SemType ??' ??? ??))
  := CURRY (ccomp FIXP (uncurry ((@CCURRY _ _ _) << (@CCURRY _ _ _)))).

(** *Definition 46: Intrinsic Semantics *)
Fixpoint InSemV (E : Env) (?? : LCtx E) (v : V E) (?? : LType) (tj : (?? v??? v ??? ??))
  : SemCtx ?? =-> SemType ?? :=
  match tj in (?? v??? v ??? ??) return SemCtx ?? =-> SemType ?? with
  | BoolRule _ ?? b                  => const (SemCtx ??) b
  | NatRule _ ?? n                   => const (SemCtx ??) n
  | VarRule _ ?? v                   => lookupV ?? v
  | FunRule _ ?? e ??' ?? tje          => FixF ?? ?? ??' t??? tje ???e
  | PairRule E ?? v v' ?? ??' tjv tjv' => PairTy t??? tjv ???v t??? tjv' ???v
  | SubsVRule E ?? v ?? ??' tjv tjl     => t??? tjl ???l << t??? tjv ???v
  end
with InSemE (E : Env) (?? : LCtx E) (e : Expr E) (?? : LType) (tj : (?? e??? e ??? ??))
     : SemCtx ?? =-> SemType ?? _BOT :=
  match tj in (?? e??? e ??? ??) return SemCtx ?? =-> SemType ?? _BOT with
  | ValRule E ?? v ?? tjv            => eta << t??? tjv ???v
  | OOpRule E ?? op e e' tje tje'   => GenBinOpTy (SemOrdOp op) t??? tje ???e t??? tje' ???e
  | BOpRule E ?? op e e' tje tje'  => GenBinOpTy (SemBoolOp op) t??? tje ???e t??? tje' ???e
  | NOpRule E ?? op e e' tje tje'   => GenBinOpTy (SemNatOp op) t??? tje ???e t??? tje' ???e
  | LetRule E ?? e e' ?? ??' tje tje' => LetTy t??? tje' ???e t??? tje ???e
  | AppRule E ?? v v' ?? ??' tjv tjv' => AppTy t??? tjv ???v t??? tjv' ???v
  | IfBRule E ?? e0 e e' ?? tje0 tje tje' => IfBTy t??? tje0 ???e t??? tje ???e t??? tje' ???e
  | FSTRule E ?? v ?? ??' tjv         => FstTy t??? tjv ???v
  | SNDRule E ?? v ?? ??' tjv         => SndTy t??? tjv ???v
  | SubsRule E ?? v ?? ??' tje tjl    => kleisli (eta << t??? tjl ???l) << t??? tje ???e
  end
where "'t???' tjv '???v'" := (InSemV tjv) and "'t???' tje '???e'" := (InSemE tje).

(** *Functions and Properties *)
Lemma InSemFun_unfold : forall (E : Env) (?? : LCtx E) (e : Expr E.+2) (?? ??' : LType)
                        (tj : (??' ?? (??' ??? ??) ?? ?? e??? e ??? ??)),
    t??? FunRule tj ???v =-= FixF ?? ?? ??' t??? tj ???e.
Proof. auto. Qed.

Lemma NatRule_simpl : forall (E : Env) (?? : LCtx E) (n : nat_cpoType) (?? : SemCtx ??),
    t??? NatRule ?? n ???v ?? =-= n.
Proof.
  auto.
Qed.

Lemma VarRule_simpl : forall (E : Env) (?? : LCtx E) (v : Var E) (?? : SemCtx ??),
    t??? VarRule ?? v ???v ?? =-= lookupV ?? v ??.
Proof.
  auto.
Qed.  

Lemma FunRule_simpl : forall (E : Env) (?? : LCtx E) (e : Expr E.+2) (?? ??' : LType)
                        (tj : (??' ?? (??' ??? ??) ?? ?? e??? e ??? ??)) (?? : SemCtx ??),
    t??? FunRule tj ???v ?? =-= fixp (exp_fun t???tj ???e << @PAIR _ (SemType ??' ??? ??) ??).
Proof.
  intros E ?? e ?? ??' tj ??.
  auto.
Qed.  

Lemma ValRule_simpl : forall (?? : LType) (E : Env) (?? : LCtx E)
                        (v : V E)
                        (tjv : (?? v??? v ??? ??))
                        (?? : SemCtx ??),
    t???ValRule tjv ???e ?? =-= eta (t??? tjv ???v ??).
Proof.
  auto.
Qed.

Lemma OOpRule_simpl : forall (op : OrdOp) (E : Env) (?? : LCtx E)
                        (e e' : Expr E)
                        (tje : (?? e??? e ??? nat??)) (tje' : (?? e??? e' ??? nat??))
                        (?? : SemCtx ??),
    t???OOpRule op tje tje' ???e ?? =-= (kleisli (eta << SimpleBOp (SemOrdOp op)))
                                  (Operator2 eta (t???tje ???e ??) (t???tje' ???e ??)).
Proof.
  auto.
Qed.

Lemma BOpRule_simpl : forall (op : BoolOp) (E : Env) (?? : LCtx E)
                        (e e' : Expr E)
                        (tje : (?? e??? e ??? bool??)) (tje' : (?? e??? e' ??? bool??))
                        (?? : SemCtx ??),
    t???BOpRule op tje tje' ???e ?? =-= (kleisli (eta << SimpleBOp (SemBoolOp op)))
                                  (Operator2 eta (t???tje ???e ??) (t???tje' ???e ??)).
Proof.
  auto.
Qed.

Lemma NOpRule_simpl : forall (op : NatOp) (E : Env) (?? : LCtx E)
                        (e e' : Expr E)
                        (tje : (?? e??? e ??? nat??)) (tje' : (?? e??? e' ??? nat??))
                        (?? : SemCtx ??),
    t???NOpRule op tje tje' ???e ?? =-= (kleisli (eta << SimpleBOp (SemNatOp op)))
                                  (Operator2 eta (t???tje ???e ??) (t???tje' ???e ??)).
Proof.
  auto.
Qed.

Lemma LetRule_simpl : forall (?? ??' : LType) (E : Env) (?? : LCtx E)
                        (e : Expr E) (e' : Expr E.+1)
                        (tje : (?? e??? e ??? ??')) (tje' : (??' ?? ?? e??? e' ??? ??))
                        (?? : SemCtx ??),
    t???LetRule tje tje' ???e ?? =-= (KLEISLIR t???tje' ???e) (??, (t???tje ???e ??)).
Proof.
  intros ?? ??' E ?? e e' tje tje' ??.
  unfold KLEISLIR. unlock. by simpl.
Qed.
  
Lemma AppRule_simpl : forall (?? ??' : LType) (E : Env) (?? : LCtx E)
                        (v v' : V E)
                        (tjv : (?? v??? v ??? ??' ??? ??)) (tjv' : (?? v??? v' ??? ??'))
                        (?? : SemCtx ??),
    t???AppRule tjv tjv' ???e ?? =-= t???tjv ???v ?? (t???tjv' ???v ??).
Proof.
  auto.
Qed.

Lemma IfZRule_simpl : forall (?? : LType) (E : Env) (?? : LCtx E)
                        (b e1 e2 : Expr E)
                        (tjb : (?? e??? b ??? bool??))
                        (tje1 : (?? e??? e1 ??? ??)) (tje2 : (?? e??? e2 ??? ??))
                        (?? : SemCtx ??),
    (t??? tjb ???e ?? =-= eta true -> t???IfBRule tjb tje1 tje2 ???e ?? =-= t??? tje1 ???e ??)
    /\
    (t??? tjb ???e ?? =-= eta false -> t???IfBRule tjb tje1 tje2 ???e ?? =-= t??? tje2 ???e ??).
Proof.
  intros ?? E ?? b e1 e2 tjb tje1 tje2 ??.
  split. intros tjb_eq_t.
  simpl. unfold id. unfold Smash. rewrite -> tjb_eq_t.
  simpl. rewrite -> Operator2_simpl. simpl.
  rewrite -> kleisliVal. simpl. rewrite -> Operator2_simpl. simpl.
  rewrite -> kleisliVal. by simpl.
  intros tjb_eq_f.
  simpl. unfold id. unfold Smash. rewrite -> tjb_eq_f. simpl.
  simpl. rewrite -> Operator2_simpl. simpl.
  rewrite -> kleisliVal. simpl. rewrite -> Operator2_simpl. simpl.
  rewrite -> kleisliVal. by simpl.
Qed.

Lemma OOpRule_Val : forall (op : OrdOp) (E : Env) (?? : LCtx E)
                      (e e' : Expr E)
                      (tje : (?? e??? e ??? nat??)) (tje' : (?? e??? e' ??? nat??))
                      (?? : SemCtx ??) (d : SemType bool??),
    t???OOpRule op tje tje' ???e ?? =-= Val d ->
    (exists n m, t??? tje ???e ?? =-= Val n
          /\ t??? tje' ???e ?? =-= Val m
          /\ (SemOrdOp op n m = d)).
Proof.
  intros op E ?? e e' tje tje' ?? d H.
  simpl in *.
  apply kleisliValVal in H.
  destruct H as [pnm [? ?]].
  simpl in *.
  apply vinj with (D:=bool_cpoType) in H0.
  unfold Smash, Operator2 in H. unlock in H. simpl in H.
  apply kleisliValVal in H.
  destruct H as [? [? ?]].
  simpl in *.
  apply kleisliValVal in H.
  apply kleisliValVal in H1.
  destruct H as [? [? ?]].
  destruct H1 as [? [? ?]].
  simpl in *.
  apply vinj with (D:=nat_cpoType -=> (nat_cpoType * nat_cpoType) _BOT) in H2.
  rewrite <- H2 in H3.
  simpl in H3.
  apply vinj with (D:=(nat_cpoType * nat_cpoType)) in H3.
  unfold id in *.
  exists x0. exists x1. split. apply H. split. apply H1.
  destruct H0. simpl in *.
  rewrite H4.
  destruct H3. destruct H3. simpl in *.
  apply f_equal3. auto. auto. auto.
Qed.

Lemma BOpRule_Val : forall (op : BoolOp) (E : Env) (?? : LCtx E)
                      (e e' : Expr E)
                      (tje : (?? e??? e ??? bool??)) (tje' : (?? e??? e' ??? bool??))
                      (?? : SemCtx ??) (d : SemType bool??),
    t???BOpRule op tje tje' ???e ?? =-= Val d ->
    (exists n m, t??? tje ???e ?? =-= Val n
          /\ t??? tje' ???e ?? =-= Val m
          /\ (SemBoolOp op n m = d)).
Proof.
  intros op E ?? e e' tje tje' ?? d H.
  simpl in *.
  apply kleisliValVal in H.
  destruct H as [pnm [? ?]].
  simpl in *.
  apply vinj with (D:=bool_cpoType) in H0.
  unfold Smash, Operator2 in H. unlock in H. simpl in H.
  apply kleisliValVal in H.
  destruct H as [? [? ?]].
  simpl in *.
  apply kleisliValVal in H.
  apply kleisliValVal in H1.
  destruct H as [? [? ?]].
  destruct H1 as [? [? ?]].
  simpl in *.
  apply vinj with (D:=bool_cpoType -=> (bool_cpoType * bool_cpoType) _BOT) in H2.
  rewrite <- H2 in H3.
  simpl in H3.
  apply vinj with (D:=(bool_cpoType * bool_cpoType)) in H3.
  unfold id in *.
  exists x0. exists x1. split. apply H. split. apply H1.
  destruct H0. simpl in *.
  rewrite H4.
  destruct H3. destruct H3. simpl in *.
  apply f_equal3. auto. auto. auto.
Qed.

Lemma NOpRule_Val : forall (op : NatOp) (E : Env) (?? : LCtx E)
                      (e e' : Expr E)
                      (tje : (?? e??? e ??? nat??)) (tje' : (?? e??? e' ??? nat??))
                      (?? : SemCtx ??) (d : SemType nat??),
    t???NOpRule op tje tje' ???e ?? =-= Val d ->
    (exists n m, t??? tje ???e ?? =-= Val n
          /\ t??? tje' ???e ?? =-= Val m
          /\ (SemNatOp op n m = d)).
Proof.
  intros op E ?? e e' tje tje' ?? d H.
  simpl in *.
  apply kleisliValVal in H.
  destruct H as [pnm [? ?]].
  simpl in *.
  apply vinj with (D:=nat_cpoType) in H0.
  unfold Smash, Operator2 in H. unlock in H. simpl in H.
  apply kleisliValVal in H.
  destruct H as [? [? ?]].
  simpl in *.
  apply kleisliValVal in H.
  apply kleisliValVal in H1.
  destruct H as [? [? ?]].
  destruct H1 as [? [? ?]].
  simpl in *.
  apply vinj with (D:=nat_cpoType -=> (nat_cpoType * nat_cpoType) _BOT) in H2.
  rewrite <- H2 in H3.
  simpl in H3.
  apply vinj with (D:=(nat_cpoType * nat_cpoType)) in H3.
  unfold id in *.
  exists x0. exists x1. split. apply H. split. apply H1.
  destruct H0. simpl in *.
  rewrite H4.
  destruct H3. destruct H3. simpl in *.
  apply f_equal3. auto. auto. auto.
Qed.
  
Lemma LET_Val : forall (?? ??' : LType) (E : Env) (?? : LCtx E)
                  (e : Expr E) (e' : Expr E.+1)
                  (tje : (?? e??? e ??? ??')) (tje' : (??' ?? ?? e??? e' ??? ??))
                  (?? : SemCtx ??) (d : SemType ??),
    t???LetRule tje tje' ???e ?? =-= Val d ->
    (exists de, t??? tje ???e ?? =-= Val de /\ t??? tje' ???e (??,de) =-= Val d).
Proof.
  intros ?? ??' E ?? e e' tje tje' ?? d H.
  simpl in H. fold SemCtx in H.
  apply kleisliValVal in H.
  destruct H as [? [? ?]]. unfold id in *.
  unfold Smash, Operator2 in H. unlock in H. simpl in H.
  apply kleisliValVal in H.
  destruct H as [? [? ?]]. simpl in *.
  rewrite -> kleisliVal in H. simpl in H.
  apply vinj with (D:=SemType ??' -=> ((SemCtx ?? * SemType ??') _BOT)) in H.
  rewrite <- H in H1.
  apply kleisliValVal in H1.
  destruct H1 as [? [? ?]]. simpl in *.
  exists x1. split. auto.
  rewrite <- H0.
  apply vinj with (D:=SemCtx ?? *  SemType ??') in H2.
    by rewrite <- H2.
Qed.

Lemma IFZ_Val : forall (?? : LType) (E : Env) (?? : LCtx E)
                  (b e1 e2 : Expr E)
                  (tjb : (?? e??? b ??? bool??))
                  (tje1 : (?? e??? e1 ??? ??)) (tje2 : (?? e??? e2 ??? ??))
                  (?? : SemCtx ??) (d : SemType ??),
    t???IfBRule tjb tje1 tje2 ???e ?? =-= Val d ->
    exists bv, t??? tjb ???e ?? =-= Val bv /\
         (bv = true -> t??? tje1 ???e ?? =-= Val d)
         /\
         (bv = false -> t??? tje2 ???e ?? =-= Val d)
.
Proof.
  intros ?? E ?? b e1 e2 tjb tje1 tje2 ?? d H.
  simpl in H. unfold Smash, Operator2, id in H. unlock in H. simpl in H.
  apply kleisliValVal in H.
  destruct H as [? [? ?]].
  apply kleisliValVal in H.
  destruct H as [? [? ?]].
  apply kleisliValVal in H.
  destruct H as [? [? ?]].
  apply kleisliValVal in H.
  destruct H as [? [? ?]].
  apply kleisliValVal in H.
  destruct H as [? [? ?]]. simpl in *.
  apply kleisliValVal in H4.
  destruct H4 as [bv [? ?]]. simpl in *.
  rewrite -> kleisliVal in H.
  rewrite -> kleisliVal in H1. simpl in *.
  apply vinj
  with (D:=bool_cpoType -=>
                      ((SemCtx ?? -=> SemType ?? _BOT)
                       *
                       (SemCtx ?? -=> SemType ?? _BOT)
                       *
                       bool_cpoType
                      ) _BOT
       ) in H.
  apply vinj with (D:=SemCtx ?? -=> SemType ?? _BOT) in H3.
  apply vinj
  with (D:=(SemCtx ??) -=> (((SemCtx ?? -=> SemType ?? _BOT) * SemCtx ??) _BOT))
    in H2.
  rewrite <- H2 in H1. clear H2. simpl in H1.
  apply vinj with (D:=(SemCtx ?? -=> SemType ?? _BOT) * SemCtx ??) in H1.
  rewrite <- H in H5. simpl in H5. clear H x3.
  apply vinj
  with (D:=(SemCtx ?? -=> SemType ?? _BOT) *
          (SemCtx ?? -=> SemType ?? _BOT) *
          bool_cpoType
       ) in H5.
  rewrite <- H3 in H1. clear H3.
  destruct H5 as [[? ?] [? ?]]. simpl in *.
  have fsteq := Ole_antisym H H3. clear H H3.
  inversion H2. clear H2 H5.
  rewrite <- H in H1. clear H.
  destruct H1 as [[? ?] [? ?]]. simpl in *.
  have fsteq' := Ole_antisym H H2. clear H H2.
  have sndeq' := Ole_antisym H1 H3. clear H1 H3.
  rewrite <- sndeq', <- fsteq' in H0. clear fsteq' sndeq'.
  destruct fsteq as [[? ?] [? ?]]. simpl in *.
  have fsteq := Ole_antisym H H2. clear H H2.
  have sndeq := Ole_antisym H1 H3. clear H1 H3.
  exists bv. split. apply H4.
  split.
  - Case "t???tjb ???e ?? = Val true".
    intro b_eq_t. rewrite -> b_eq_t in H0.
    rewrite <- H0. simpl. by rewrite <- fsteq.
  - Case "t???tjb ???e ?? > Val false".
    intros b_eq_f. rewrite -> b_eq_f in H0.
    rewrite <- H0. simpl. by rewrite <- sndeq.
Qed.

Lemma OOpRule_Val2 :
    forall (op : OrdOp) (E : Env) (?? : LCtx E)
                      (e e' : Expr E)
                      (tje : (?? e??? e ??? nat??)) (tje' : (?? e??? e' ??? nat??))
                      (?? : SemCtx ??) (n m : nat),
      t??? tje ???e ?? =-= Val n /\ t??? tje' ???e ?? =-= Val m
      ->
      t???OOpRule op tje tje' ???e ?? =-= Val (SemOrdOp op n m).
Proof.
  intros op E ?? e e' tje tje' ?? n m H.
  destruct H.
  simpl. unfold Smash, id.
  rewrite -> H.
  rewrite -> H0.
  rewrite -> Operator2_simpl. simpl.
  by rewrite -> kleisliVal.
Qed.

Lemma BOpRule_Val2 :
    forall (op : BoolOp) (E : Env) (?? : LCtx E)
                      (e e' : Expr E)
                      (tje : (?? e??? e ??? bool??)) (tje' : (?? e??? e' ??? bool??))
                      (?? : SemCtx ??) (n m : bool),
      t??? tje ???e ?? =-= Val n /\ t??? tje' ???e ?? =-= Val m
      ->
      t???BOpRule op tje tje' ???e ?? =-= Val (SemBoolOp op n m).
Proof.
  intros op E ?? e e' tje tje' ?? n m H.
  destruct H.
  simpl. unfold Smash, id.
  rewrite -> H.
  rewrite -> H0.
  rewrite -> Operator2_simpl. simpl.
  by rewrite -> kleisliVal.
Qed.

Lemma NOpRule_Val2 :
    forall (op : NatOp) (E : Env) (?? : LCtx E)
                      (e e' : Expr E)
                      (tje : (?? e??? e ??? nat??)) (tje' : (?? e??? e' ??? nat??))
                      (?? : SemCtx ??) (n m : nat),
      t??? tje ???e ?? =-= Val n /\ t??? tje' ???e ?? =-= Val m
      ->
      t???NOpRule op tje tje' ???e ?? =-= Val (SemNatOp op n m).
Proof.
  intros op E ?? e e' tje tje' ?? n m H.
  destruct H.
  simpl. unfold Smash, id.
  rewrite -> H.
  rewrite -> H0.
  rewrite -> Operator2_simpl. simpl.
  by rewrite -> kleisliVal.
Qed.
