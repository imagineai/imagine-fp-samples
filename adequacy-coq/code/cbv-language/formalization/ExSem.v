
(*begin hide*)
Add LoadPath "../domain-theory".

Require Import Utils.
Require Import Program.
Require Import Lang.

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

Require Import DomainStuff.
Require Import PredomAll.
Require Import PredomProd.
Require Import Domains.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.
(*end hide*)

(** *)
(*** Chapter 4: Extended Language Semantics ***)
(** *)

(** *Environment Semantics *)
Fixpoint SemEnv E : cpoType :=
  match E with
  | O => One
  | S E => SemEnv E * VInf
  end.

(** *Variable Semantics *)
Fixpoint SemVar E (v : Var E) : SemEnv E =-> VInf :=
  match v with 
  | ZVAR _   => pi2
  | SVAR _ v => SemVar v << pi1
  end.

(** *Notation *)
Notation "η !! v" := (@SemVar _ v η) (at level 1, no associativity).
Notation "↑⊥ v" := (eta v) (at level 1, left associativity).
(* Notation "↑int n" := (inl n) (at level 1, left associativity). *)
(* Notation "↑i⊥ n" := (↑⊥ (↑int n)) (at level 1, left associativity). *)
Notation "⊥" := PBot.

(** *Auxiliar functions *)
Definition F (E : Env) (SemE : SemEnv E.+2 =-> VInf _BOT) :
  SemEnv E -=> ((DInf -=> DInf _BOT) -=> (DInf -=> DInf _BOT))
  := exp_fun
      (exp_fun
         (kleisli (eta << Roll) <<
                  SemE << ((Id >< inFun) >< Unroll))).

Definition mod2 (n : nat) : nat_cpoType :=
  PeanoNat.Nat.modulo n 2.

Definition MOD2 : nat_cpoType =-> nat_cpoType := SimpleUOp mod2.

Definition VInfToBool : VInf -=> bool_cpoType _BOT :=
  [| [| N_to_B , const _ ⊥ |] , const _ ⊥ |].

Definition VInfToNat : VInf -=> nat_cpoType _BOT :=
  [| [| eta , const _ ⊥ |] , const _ ⊥ |].

Definition VInfToFun : VInf -=> (DInf -=> DInf _BOT) _BOT :=
  [| [| const _ ⊥, eta |] , const _ ⊥ |].

Definition VInfToPair : VInf -=> (DInf * DInf) _BOT :=
  [| const _ ⊥, eta |].

Definition GenBinOp (A B : Type) (C : cpoType) (E : Env)
           (inC  : C =-> VInf)
           (outA : VInf =-> discrete_cpoType A _BOT)
           (outB : VInf =-> discrete_cpoType B _BOT)
           (op : A -> B -> C)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT :=
  (kleisli (eta << inC << SimpleBOp op) << uncurry (Smash _ _))
    << <| kleisli outA << d1
        , kleisli outB << d2
|>.
Arguments GenBinOp [A B C E] _ _ _ _ _.

Definition GenBinOp_DInf (A B : Type) (C : cpoType) (E : Env)
           (inC  : C =-> VInf)
           (outA : VInf =-> discrete_cpoType A _BOT)
           (outB : VInf =-> discrete_cpoType B _BOT)
           (op : A -> B -> C)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT :=
  (kleisli (eta << inC << SimpleBOp op) << uncurry (Smash _ _))
    << <| kleisli (outA << Unroll) << KR << d1
  , kleisli (outB << Unroll) << KR << d2  
            |>.
Arguments GenBinOp_DInf [A B C E] _ _ _ _ _.

Definition GenOrdOp {E : Env}
           (op : nat -> nat -> bool)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT := GenBinOp (inNat << B_to_N)
                                    VInfToNat VInfToNat op d1 d2.

Definition GenBoolOp {E : Env}
           (op : bool -> bool -> bool)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT := GenBinOp (inNat << B_to_N)
                                    (VInfToBool) (VInfToBool) op d1 d2.

Definition GenNatOp {E : Env}
           (op : nat -> nat -> nat)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT := GenBinOp inNat VInfToNat VInfToNat op d1 d2.

Definition GenOrdOp_DInf {E : Env}
           (op : nat -> nat -> bool)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT := GenBinOp_DInf (inNat << B_to_N)
                                         VInfToNat VInfToNat op d1 d2.

Definition GenBoolOp_DInf {E : Env}
           (op : bool -> bool -> bool)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT := GenBinOp_DInf (inNat << B_to_N)
                                         VInfToBool VInfToBool op d1 d2.

Definition GenNatOp_DInf {E : Env}
           (op : nat -> nat -> nat)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT := GenBinOp_DInf inNat VInfToNat VInfToNat op d1 d2.

Definition LetApp {E : Env}
           (d1 : SemEnv E.+1 =-> VInf _BOT)
           (d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT := ev << <| exp_fun (KLEISLIR d1), d2 |>
.

Definition LetAppDInf (E : Env)
           (d1 : SemEnv E.+1 =-> VInf _BOT)
           (d2 : SemEnv E =-> VInf _BOT) :=
  KR << ev << <| exp_fun (KLEISLIR (d1 << Id >< Unroll)), KR << d2 |>.


Definition AppOp {E : Env}
           (d1 : SemEnv E =-> VInf)
           (d2 : SemEnv E =-> VInf) : SemEnv E =-> VInf _BOT :=
  KLEISLI (eta << Unroll) << (KLEISLIL ev) <<
          <| VInfToFun << d1, Roll << d2 |>.

Definition IfBOp {E : Env}
           (b  : SemEnv E =-> VInf _BOT)
           (d1 : SemEnv E =-> VInf _BOT)
           (d2 : SemEnv E =-> VInf _BOT) : SemEnv E =-> VInf _BOT
  := ev
    <<
    <| pi1 << pi1 , <| pi2 << pi1 , pi2 |> |>
    <<
    <| <| const (SemEnv E)
          (KLEISLIL (UNCURRY
                 ((CCURRY (CCURRY (IfB (SemEnv E) (VInf _BOT)))) d1 d2)))
    , kleisli VInfToBool << b
        |>
    , Id
    |>
.

Definition IfZOp {E : Env}
           (b  : SemEnv E =-> VInf _BOT)
           (d1 : SemEnv E =-> VInf _BOT)
           (d2 : SemEnv E =-> VInf _BOT) : SemEnv E =-> VInf _BOT
  := ev
    <<
    <| pi1 << pi1 , <| pi2 << pi1 , pi2 |> |>
    <<
    <| <| const (SemEnv E)
          (KLEISLIL (UNCURRY
                 ((CCURRY (CCURRY (IfZ (SemEnv E) (VInf _BOT)))) d1 d2)))
    , kleisli VInfToNat << b
        |>
    , Id
    |>
.

Definition IfOneOp {E : Env}
           (b  : SemEnv E =-> VInf _BOT)
           (d1 : SemEnv E =-> VInf _BOT)
           (d2 : SemEnv E =-> VInf _BOT) : SemEnv E =-> VInf _BOT
  := IfZOp b d2 d1.

Definition PairOp {E : Env}
           (d1 : SemEnv E =-> VInf)
           (d2 : SemEnv E =-> VInf) : SemEnv E =-> VInf
  := inPair << (Roll >< Roll) << prod_morph (d1, d2) << <|Id, Id|>.

Definition FSTOp {E : Env}
           (v  : SemEnv E =-> VInf) : SemEnv E =-> VInf _BOT
  := kleisli (eta << Unroll << pi1) << VInfToPair << v.

Definition SNDOp {E : Env}
           (v  : SemEnv E =-> VInf) : SemEnv E =-> VInf _BOT
  := kleisli (eta << Unroll << pi2) << VInfToPair << v.

(** *Notation *)
Notation "'⦓' op '⦔'"    := (GenNatOp op) (at level 1, left associativity).
Infix "⊥⊥⃑" := LetApp (at level 1, no associativity) .
Infix "↓f"   := AppOp (at level 1, no associativity) .

(** Notation *)
Reserved Notation "⟦ v '⟧v'" (at level 1, no associativity).
Reserved Notation "⟦ e '⟧e'" (at level 1, no associativity).

(** *Definition 40: Extrinsic Semantics *)
Fixpoint SemV E (v:V E) : SemEnv E =-> VInf :=
  match v return SemEnv E =-> VInf with
  | BOOL b       => inNat << const _ (B_to_N b)
  | NAT i        => inNat << const _ i
  | VAR m        => SemVar m
  | FUN e        => inFun << FIXP << (F ⟦ e ⟧e)
  | VPAIR v1 v2  => PairOp ⟦ v1 ⟧v ⟦ v2 ⟧v
  end
with SemE E (e: Expr E) : SemEnv E =-> VInf _BOT :=
  match e with
  | VAL v        => eta << ⟦ v ⟧v
  | APP v1 v2    => (⟦ v1 ⟧v)↓f ⟦ v2 ⟧v
  | OOp op e1 e2 => GenOrdOp (SemOrdOp op) ⟦ e1 ⟧e ⟦ e2 ⟧e
  | BOp op e1 e2 => GenBoolOp (SemBoolOp op) ⟦ e1 ⟧e ⟦ e2 ⟧e
  | NOp op e1 e2 => ⦓SemNatOp op⦔ ⟦ e1 ⟧e ⟦ e2 ⟧e
  | LET e1 e2    => ⟦ e2 ⟧e⊥⊥⃑ ⟦ e1 ⟧e
  | IFB e0 e1 e2 => IfOneOp ⟦ e0 ⟧e ⟦ e1 ⟧e ⟦ e2 ⟧e
  | EFST v       => FSTOp ⟦ v ⟧v
  | ESND v       => SNDOp ⟦ v ⟧v
  end
where "⟦ e ⟧e" := (SemE e) and "⟦ v ⟧v" := (SemV v).

(** *Notation and properties *)
Notation "↑f f" := (inFun f) (at level 1, left associativity).
Notation "↑n n" := (inNat n) (at level 1, left associativity).
Notation "↑p p" := (inPair p) (at level 1, left associativity).
Notation "↑⊥ v"   := (eta v) (at level 1, left associativity).
Notation "↑n⊥ n"  := (↑⊥ (↑n n)) (at level 1, left associativity).
Notation "↑f⊥ f"  := (↑⊥ (↑f f)) (at level 1, left associativity).
Notation "↑p⊥ p"  := (↑⊥ (↑p p)) (at level 1, left associativity).

Lemma SmashLemmaValVal :
  forall A B (d : A _BOT) (d' : B _BOT)
    (v : A) (v' : B),
    d =-= ↑⊥ v /\ d' =-= ↑⊥ v' ->
    (((Smash A B) d) d') =-= ↑⊥ (v , v').
Proof.
  intros A B d d' v v' H.
  inversion H. unfold Smash.
  rewrite -> H0. rewrite -> H1.
  simpl. by rewrite -> Operator2_simpl.
Qed.

Lemma OrdOpLemma: forall (op : OrdOp) (e e' : Expr 0) (n m : nat) (η : SemEnv 0),
    ⟦ e ⟧e η =-= ↑n⊥ n /\ ⟦ e' ⟧e η =-= ↑n⊥ m ->
    ⟦ OOp op e e' ⟧e η =-= eta (inNat (B_to_N (SemOrdOp op n m))).
Proof.
  intros op d d' n m η H.
  destruct H as [Hd  Hd' ].
  simpl. rewrite -> Hd. rewrite -> Hd'.
  simpl. unfold VInfToNat.
  repeat (rewrite -> kleisliVal) ; repeat (rewrite SUM_fun_simplx).
  simpl.
  rewrite -> SmashLemmaValVal. rewrite -> kleisli_simpl. rewrite -> kleisli_inv.
  simpl. auto.  auto.
Qed.

Lemma BoolOpLemma: forall (op : BoolOp) (e e' : Expr 0) (bn bm : bool) (η : SemEnv 0),
    ⟦ e ⟧e η =-= eta (inNat (B_to_N bn)) /\ ⟦ e' ⟧e η =-= eta (inNat (B_to_N bm)) ->
    ⟦ BOp op e e' ⟧e η =-= eta (inNat (B_to_N (SemBoolOp op bn bm))).
Proof.
  intros op d d' bn bm η H.
  destruct H as [Hd  Hd' ].
  simpl. rewrite -> Hd. rewrite -> Hd'.
  simpl. unfold VInfToBool.
  repeat (rewrite -> kleisliVal) ; repeat (rewrite SUM_fun_simplx).
  simpl.
  rewrite -> SmashLemmaValVal. rewrite -> kleisli_simpl. rewrite -> kleisli_inv.
  simpl. auto. split.
  destruct bn; simpl; auto.
  destruct bm; simpl; auto.
Qed.

Lemma NatOpLemma: forall (op : NatOp) (e e' : Expr 0) (n m : nat) (η : SemEnv 0),
    ⟦ e ⟧e η =-= ↑n⊥ n /\ ⟦ e' ⟧e η =-= ↑n⊥ m ->
    ⟦ NOp op e e' ⟧e η =-= ↑n⊥ (SemNatOp op n m).
Proof.
  intros op d d' n m η H.
  destruct H as [Hd  Hd' ].
  simpl. rewrite -> Hd. rewrite -> Hd'.
  simpl. unfold VInfToNat.
  repeat (rewrite -> kleisliVal) ; repeat (rewrite SUM_fun_simplx).
  simpl.
  rewrite -> SmashLemmaValVal. rewrite -> kleisli_simpl. rewrite -> kleisli_inv.
  simpl. auto.  auto.
Qed.

Lemma StepLemma :
  forall {A B C} (f : cpoCatType (A * B) C) (g : cpoCatType A B),
    (ev << <| exp_fun f , g |>) =-= f <<  <| Id , g |>.
Proof.
  intros A B C f g.
  assert (Fid : exp_fun f =-= exp_fun f << Id) by
      (rewrite -> comp_idR; reflexivity).
  assert (Gid : g =-= Id << g) by
      (rewrite -> comp_idL; reflexivity).
  rewrite -> Fid at 1 ; 
    rewrite -> Gid at 1.
  rewrite -> prod_fun_compr.
  rewrite -> comp_assoc.
    by rewrite exp_com.
Qed.

Lemma SemVal_VAR_equation : forall (E : Env) (η : SemEnv E) (v : Var E),
    SemV (VAR v) η =-= SemVar v η.
Proof.
  intros E η v. by unfold SemV.
Qed.

Lemma SemVal_INT_equation : forall (E : Env) (η : SemEnv E) (n : nat),
    SemV (NAT n) η =-= inNat n.
Proof.
  intros E env n. by unfold SemV.
Qed.

Lemma SemVal_FUN_equation : forall (E : Env) (η : SemEnv E) (e : Expr E.+2),
    ⟦ FUN e ⟧v η =-= ↑f (((F ⟦e ⟧e) η) (FIXP ((F ⟦e ⟧e) η))).
Proof.
  intros E η e.
  unfold "⟦ _ ⟧v" at 1. fold ⟦ e ⟧e.
  rewrite -> comp_simpl.
  rewrite -> comp_simpl.
  eapply tset_trans. rewrite -> FIXP_eq. apply tset_refl.
  auto.
Qed.

Lemma SemExp_VAL_equation : forall (E : Env) (η : SemEnv E) (v : V E),
    ⟦ VAL v ⟧e η =-= ↑⊥ (⟦ v ⟧v η).
Proof.
  by simpl.
Qed.

Lemma SemExp_OrdOp_equationNatNat :
  forall (E : Env) (η : SemEnv E) (op : OrdOp)
    (e e' : Expr E) (n m : nat),
    ⟦ e ⟧e η =-= ↑n⊥ n /\ ⟦ e' ⟧e η =-= ↑n⊥ m ->
    ⟦ OOp op e e' ⟧e η =-= eta (inNat (B_to_N (SemOrdOp op n m))).
Proof.
  intros E η op d d' n m H.
  destruct E.
  apply OrdOpLemma. apply H.
  inversion H.
  simpl.
  rewrite -> H0.
  rewrite -> H1.
  unfold VInfToBool.
  simpl.
  rewrite -> kleisliVal.
  rewrite -> kleisliVal.
  do 2 setoid_rewrite -> SUM_fun_simplx.
  rewrite -> SmashLemmaValVal.
  rewrite -> kleisli_simpl.
  simpl.
  rewrite -> kleisli_inv.
  simpl.
  apply tset_refl.
  by split.
Qed.

Lemma SemExp_BoolOp_equationNatNat :
  forall (E : Env) (η : SemEnv E) (op : BoolOp)
    (e e' : Expr E) (bn bm : bool),
    ⟦ e ⟧e η =-= eta (inNat (B_to_N bn)) /\ ⟦ e' ⟧e η =-= eta (inNat (B_to_N bm)) ->
    ⟦ BOp op e e' ⟧e η =-= eta (inNat (B_to_N (SemBoolOp op bn bm))).
Proof.
  intros E η op e e' bn bm H.
  destruct E.
  apply BoolOpLemma. apply H.
  inversion H.
  simpl.
  rewrite -> H0.
  rewrite -> H1.
  simpl.
  rewrite -> kleisliVal.
  rewrite -> kleisliVal.
  do 2 setoid_rewrite -> SUM_fun_simplx.
  rewrite -> SmashLemmaValVal.
  rewrite -> kleisli_simpl.
  simpl.
  rewrite -> kleisli_inv.
  simpl.
  apply tset_refl.
  split.
  destruct bn; simpl; auto.
  destruct bm; simpl; auto.  
Qed.

Lemma SemExp_NatOp_equationNatNat :
  forall (E : Env) (η : SemEnv E) (op : NatOp)
    (e e' : Expr E) (n m : nat),
    ⟦ e ⟧e η =-= ↑n⊥ n /\ ⟦ e' ⟧e η =-= ↑n⊥ m ->
    ⟦ NOp op e e' ⟧e η =-= ↑n⊥ (SemNatOp op n m).
Proof.
  intros E η op d d' n m H.
  destruct E.
  apply NatOpLemma. apply H.
  inversion H.
  simpl.
  rewrite -> H0.
  rewrite -> H1.
  unfold VInfToNat.
  simpl.
  rewrite -> kleisliVal.
  rewrite -> kleisliVal.
  do 2 setoid_rewrite -> SUM_fun_simplx.
  rewrite -> SmashLemmaValVal.
  rewrite -> kleisli_simpl.
  simpl.
  rewrite -> kleisli_inv.
  simpl.
  apply tset_refl.
  by split.
Qed.

Lemma SmashLemma_Bot :
  forall A B (d : A _BOT) (d' : B _BOT),
    d =-= ⊥ \/ d' =-= ⊥ ->
    (((Smash A B) d) d') =-= ⊥.
Proof.
  intros A B d d' H.
  inversion H.
  - (* Case "d =-= ⊥". *)
    unfold Smash.
    rewrite -> H0.
    by rewrite -> Operator2_strictL.
  - (* Case "d' =-= ⊥". *)
    unfold Smash.
    rewrite -> H0.
    by rewrite -> Operator2_strictR.
Qed.

Lemma SemExp_NatOp_equation_Bot :
  forall (E : Env) (η : SemEnv E) (op : NatOp)
    (e e' : Expr E),
    ⟦ e ⟧e η =-= ⊥ \/ ⟦ e' ⟧e η =-= ⊥ ->
    ⟦ NOp op e e'⟧e η =-= ⊥.
Proof.
  intros E η op d d' H.
  inversion H.
  - Case "(SemE d) η =-= ⊥".
    simpl.
    unfold VInfToNat.
    rewrite -> H0.
    rewrite -> kleisli_bot.
    rewrite -> SmashLemma_Bot.
    2 : { SCase "Hypothesis SmashLemma_Bot".
            by left.
    }
      by rewrite -> kleisli_bot.
  - Case "(SemE d') η =-= ⊥".
    simpl.
    unfold VInfToNat.
    rewrite -> H0.
    rewrite -> kleisli_bot.
    rewrite -> SmashLemma_Bot.
    2 : { SCase "Hypothesis SmashLemma_Bot".
            by right.
    }
      by rewrite -> kleisli_bot.
Qed.

Lemma SemExp_OrdOp_equation_Bot :
  forall (E : Env) (η : SemEnv E) (op : OrdOp)
    (e e' : Expr E),
    ⟦ e ⟧e η =-= ⊥ \/ ⟦ e' ⟧e η =-= ⊥ ->
    ⟦ OOp op e e'⟧e η =-= ⊥.
Proof.
  intros E η op d d' H.
  inversion H.
  - Case "(SemE d) η =-= ⊥".
    simpl.
    rewrite -> H0.
    rewrite -> kleisli_bot.
    rewrite -> SmashLemma_Bot.
    2 : { SCase "Hypothesis SmashLemma_Bot".
            by left.
    }
      by rewrite -> kleisli_bot.
  - Case "(SemE d') η =-= ⊥".
    simpl.
    rewrite -> H0.
    rewrite -> kleisli_bot.
    rewrite -> SmashLemma_Bot.
    2 : { SCase "Hypothesis SmashLemma_Bot".
            by right.
    }
      by rewrite -> kleisli_bot.
Qed.

Lemma SemExp_BoolOp_equation_Bot :
  forall (E : Env) (η : SemEnv E) (op : BoolOp)
    (e e' : Expr E),
    ⟦ e ⟧e η =-= ⊥ \/ ⟦ e' ⟧e η =-= ⊥ ->
    ⟦ BOp op e e'⟧e η =-= ⊥.
Proof.
  intros E η op d d' H.
  inversion H.
  - Case "(SemE d) η =-= ⊥".
    simpl.
    rewrite -> H0.
    rewrite -> kleisli_bot.
    rewrite -> SmashLemma_Bot.
    2 : { SCase "Hypothesis SmashLemma_Bot".
            by left.
    }
      by rewrite -> kleisli_bot.
  - Case "(SemE d') η =-= ⊥".
    simpl.
    rewrite -> H0.
    rewrite -> kleisli_bot.
    rewrite -> SmashLemma_Bot.
    2 : { SCase "Hypothesis SmashLemma_Bot".
            by right.
    }
      by rewrite -> kleisli_bot.
Qed.

Lemma SemExp_LET_equation_Bot :
  forall (E : Env) (η : SemEnv E)
    (e : Expr E) (e' : Expr E.+1),
    ⟦ e ⟧e η =-= ⊥ -> ⟦ LET e e' ⟧e η =-= ⊥.
Proof.
  intros E env d d' H.
  simpl. rewrite -> H.
  unlock KLEISLIR. simpl.
  unfold id.
  rewrite -> SmashLemma_Bot.
  rewrite -> kleisli_bot.
  reflexivity.
  - Case "Hypothesis SmashLemma_Bot".
    by right. 
Qed.
      
Lemma SemExp_LET_equationVal :
  forall (E : Env) (η : SemEnv E) (v : VInf) (e : Expr E) (e' : Expr E.+1),
    ⟦ e ⟧e η =-= ↑⊥ v -> ⟦ LET e e' ⟧e η =-= ⟦ e' ⟧e (η, v).
Proof.
  intros E env v d d' H.
  simpl. rewrite -> H.
  simpl. unlock KLEISLIR.
  simpl. unfold id.
  rewrite -> SmashLemmaValVal.
  2 : { Case "Hypothesis SmashLemmaValVal".
        by simpl.
  }
  simpl.
  by rewrite -> kleisliVal.
Qed.

Lemma INL_convert : forall (A B : cpoType) (a : A),
    @INL A B a =-= inl a.
Proof.
  auto.
Qed.

Lemma SemExp_OrdOp_equationNatNat2 :
  forall (E : Env) (η : SemEnv E) (op : OrdOp)
    (e e' : Expr E) (nm : VInf),
    ⟦ OOp op e e' ⟧e η =-= Val nm ->
    (exists n m, ⟦ e ⟧e η =-= ↑n⊥ n
          /\ ⟦ e' ⟧e η =-= ↑n⊥ m
          /\ (inNat (B_to_N (SemOrdOp op n m)) =-= nm)).
Proof.
  intros E η op e e' nm H.
  simpl in H.
  apply kleisliValVal in H.
  destruct H as [s [? ?]].
  unfold Smash in *. unfold Operator2 in *. unlock in H.
  simpl in *.
  apply kleisliValVal in H.
  destruct H as [ope [? ?]].
  simpl in *.
  apply kleisliValVal in H1.
  destruct H1 as [? [? ?]].
  apply kleisliValVal in H1.
  destruct H1 as [se' [? ?]].
  apply kleisliValVal in H.
  destruct H as [? [? ?]].
  simpl in *.
  apply kleisliValVal in H.
  destruct H as [se [? ?]].
  simpl in *.
  destruct se as [[n | f] | p].
  - Case "Nat".
    destruct se' as [[n' | f'] | p'].
    + SCase "Nat".
      do 2 setoid_rewrite -> SUM_fun_simplx in H5.
      do 2 setoid_rewrite -> SUM_fun_simplx in H3.
      exists n, n'. split. apply H. split. apply H1. simpl in H5, H3.
      apply vinj with (D:=VInf) in H0.
      apply vinj with (D:=nat_cpoType) in H5.
      apply vinj with (D:=nat_cpoType) in H3.
      apply vinj in H4. rewrite <- H4 in H2.
      rewrite <- H3 in H2.  simpl in H2. destruct s as [n1 n2]. simpl in H0.
      apply vinj with (D:= nat_cpoType * nat_cpoType) in H2. rewrite <- H5 in H2.
      apply pairInj_eq in H2 as [? ?].
      rewrite <- H0.
      destruct H2. simpl in H2.
      destruct H6. simpl in H6.
      rewrite -> H2. rewrite -> H6. auto.
    + SCase "Fun".
      do 2 setoid_rewrite -> SUM_fun_simplx in H3. simpl in H3.
      apply tset_sym in H3. apply PBot_incon_eq in H3. inversion H3.
    + SCase "Pair".
      setoid_rewrite -> SUM_fun_simplx in H3. simpl in H3.
      apply tset_sym in H3. apply PBot_incon_eq in H3. inversion H3.
  - SCase "Fun".
    do 2 setoid_rewrite -> SUM_fun_simplx in H5. simpl in H5.
    apply tset_sym in H5. apply PBot_incon_eq in H5. inversion H5.
  - SCase "Pair".
    setoid_rewrite -> SUM_fun_simplx in H5. simpl in H5.
    apply tset_sym in H5. apply PBot_incon_eq in H5. inversion H5.
Qed.

Lemma VInfToBool_prop : forall (vb : VInf) (b : bool),
    VInfToBool vb =-= Val b -> vb =-= inNat (B_to_N b).
Proof.
  intros vb b H.
  destruct vb as [[n | f] | p].
  destruct n. do 2 setoid_rewrite -> SUM_fun_simplx in H.
  simpl in H. apply vinj with (D:=bool_cpoType) in H.
  rewrite <- H. by simpl.
  destruct n. do 2 setoid_rewrite -> SUM_fun_simplx in H.
  simpl in H. apply vinj with (D:=bool_cpoType) in H.
  rewrite <- H. by simpl.
  do 2 setoid_rewrite -> SUM_fun_simplx in H.
  simpl in H. symmetry in H. apply PBot_incon_eq in H. inversion H.
  do 2 setoid_rewrite -> SUM_fun_simplx in H.
  simpl in H. symmetry in H. apply PBot_incon_eq in H. inversion H.
  setoid_rewrite -> SUM_fun_simplx in H.
  simpl in H. symmetry in H. apply PBot_incon_eq in H. inversion H.
Qed.

Lemma SemExp_BoolOp_equationNatNat2 :
  forall (E : Env) (η : SemEnv E) (op : BoolOp)
    (e e' : Expr E) (nm : VInf),
    ⟦ BOp op e e' ⟧e η =-= Val nm ->
    (exists bn bm, ⟦ e ⟧e η =-= eta (inNat (B_to_N bn))
            /\ ⟦ e' ⟧e η =-= eta (inNat (B_to_N bm))
            /\ (inNat (B_to_N (SemBoolOp op bn bm)) =-= nm)).
Proof.
  intros E η op e e' bnbm H.
  simpl in H.
  apply kleisliValVal in H.
  destruct H as [[s1 s2] [? ?]].
  apply SmashInv in H as [? ?].
  symmetry in H, H1.
  apply kleisliValVal in H as [? [? ?]].
  apply kleisliValVal in H1 as [? [? ?]].
  exists s1, s2. split. rewrite -> H. apply Val_eq_compat.
  apply VInfToBool_prop in H2. by rewrite -> H2.
  split.
  rewrite -> H1. apply Val_eq_compat.
  apply VInfToBool_prop in H3. by rewrite -> H3.
  apply vinj in H0. by rewrite <- H0.
Qed.

Lemma SemExp_NatOp_equationNatNat2 :
  forall (E : Env) (η : SemEnv E) (op : NatOp)
    (e e' : Expr E) (nm : VInf),
    ⟦NOp op e e' ⟧e η =-= Val nm ->
    (exists n m, ⟦ e ⟧e η =-= ↑n⊥ n
          /\ ⟦ e' ⟧e η =-= ↑n⊥ m
          /\ (inNat (SemNatOp op n m) =-= nm)).
Proof.
  intros E η op e e' nm H.
  simpl in H.
  apply kleisliValVal in H.
  destruct H as [s [? ?]].
  unfold Smash in *. unfold Operator2 in *. unlock in H.
  simpl in *.
  apply kleisliValVal in H.
  destruct H as [ope [? ?]].
  simpl in *.
  apply kleisliValVal in H1.
  destruct H1 as [? [? ?]].
  apply kleisliValVal in H1.
  destruct H1 as [se' [? ?]].
  apply kleisliValVal in H.
  destruct H as [? [? ?]].
  simpl in *.
  apply kleisliValVal in H.
  destruct H as [se [? ?]].
  simpl in *.
  destruct se as [[n | f] | p].
  - Case "Nat".
    destruct se' as [[n' | f'] | p'].
    + SCase "Nat".
      do 2 setoid_rewrite -> SUM_fun_simplx in H5.
      do 2 setoid_rewrite -> SUM_fun_simplx in H3.
      exists n, n'. split. apply H. split. apply H1. simpl in H5, H3.
      apply vinj with (D:=VInf) in H0.
      apply vinj with (D:=nat_cpoType) in H5.
      apply vinj with (D:=nat_cpoType) in H3.
      apply vinj in H4. rewrite <- H4 in H2.
      rewrite <- H3 in H2.  simpl in H2. destruct s as [n1 n2]. simpl in H0.
      apply vinj with (D:= nat_cpoType * nat_cpoType) in H2. rewrite <- H5 in H2.
      apply pairInj_eq in H2 as [? ?].
      rewrite <- H0.
      destruct H2. simpl in H2.
      destruct H6. simpl in H6.
      rewrite -> H2. rewrite -> H6. auto.
    + SCase "Fun".
      do 2 setoid_rewrite -> SUM_fun_simplx in H3. simpl in H3.
      apply tset_sym in H3. apply PBot_incon_eq in H3. inversion H3.
    + SCase "Pair".
      setoid_rewrite -> SUM_fun_simplx in H3. simpl in H3.
      apply tset_sym in H3. apply PBot_incon_eq in H3. inversion H3.
  - SCase "Fun".
    do 2 setoid_rewrite -> SUM_fun_simplx in H5. simpl in H5.
    apply tset_sym in H5. apply PBot_incon_eq in H5. inversion H5.
  - SCase "Pair".
    setoid_rewrite -> SUM_fun_simplx in H5. simpl in H5.
    apply tset_sym in H5. apply PBot_incon_eq in H5. inversion H5.
Qed.

Lemma SemExp_LET_equationVal2 :
  forall (E : Env) (η : SemEnv E)
    (e : Expr E) (e' : Expr E.+1) (d : VInf),
    ⟦LET e e' ⟧e η =-= Val d ->
    (exists de, ⟦ e ⟧e η =-= Val de /\ ⟦ e' ⟧e (η,de) =-= Val d).
Proof.
  intros E η e e' d H.
  simpl in *.
  unfold KLEISLIR in H. unlock in H. simpl in H. fold SemEnv in H.
  unfold id in H.
  apply kleisliValVal in H.
  destruct H as [? [? ?]]. simpl in *.
  unfold Smash, Operator2 in H. unlock in H. simpl in H.
  apply kleisliValVal in H.
  destruct H as [? [? ?]].
  apply kleisliValVal in H.
  destruct H as [? [? ?]]. simpl in *.
  apply vinj with (D:=VInf -=> (SemEnv E * VInf) _BOT) in H2.
  rewrite <- H2 in H1.
  apply kleisliValVal in H1.
  destruct H1 as [? [? ?]]. simpl in *.
  exists x2. split. auto.
  rewrite <- H0.
  apply vinj with (D:=SemEnv E * VInf) in H3.
  rewrite <- H3.
  apply vinj with (D:=SemEnv E) in H.
    by rewrite H.
Qed.

Lemma SemExp_IFZ_equationVal2 :
  forall (E : Env) (η : SemEnv E)
    (b e1 e2 : Expr E) (d : VInf),
    ⟦IFB b e1 e2 ⟧e η =-= Val d ->
    exists bv, ⟦ b ⟧e η =-= Val (inNat bv) /\
         (bv = B_to_N true -> ⟦ e1 ⟧e η =-= Val d)
         /\
         (bv = B_to_N false -> ⟦ e2 ⟧e η =-= Val d).
Proof.
  intros E η b e1 e2 d H.
  simpl in H. unfold KLEISLIL in H. unlock in H. simpl in H.
  unfold Smash, Operator2, id in H. unlock in H. simpl in H.
  apply kleisliValVal in H.
  destruct H as [? [? ?]]. simpl in *.
  apply kleisliValVal in H.
  destruct H as [? [? ?]].
  apply kleisliValVal in H.
  destruct H as [n [? ?]]. simpl in *.
  apply kleisliValVal in H1. destruct H1 as [? [? ?]].
  apply kleisliValVal in H. destruct H as [? [? ?]].
  destruct x2 as [[n' | f] | p].
  - Case "Nat".
    apply vinj with (D:=SemEnv E -=> (nat_cpoType * SemEnv E) _BOT) in H2.
    rewrite <- H2 in H3. clear H2.
    simpl in H3.
    apply vinj with (D:=nat_cpoType * SemEnv E) in H3.
    apply vinj with (D:=SemEnv E) in H1. rewrite <- H1 in H3.
    destruct H3 as [[? ?] [? ?]]. simpl in *. inversion H2. rewrite <- H7 in H0.
    clear H1 H2 H5 H7.
    have sndeq := Ole_antisym H3 H6. clear H3 H6.
    do 2 setoid_rewrite -> SUM_fun_simplx in H4.
    apply vinj with (D:=nat_cpoType) in H4. setoid_rewrite <- H4 in H0.
    exists n'. split. auto.
    split.
    + SCase "⟦b ⟧e η = Val true".
      intros b_eq_0. rewrite -> b_eq_0 in *.
      rewrite <- H0. simpl. by rewrite <- sndeq.
    + SCase "⟦b ⟧e η > Val false".
      intros b_eq_0. rewrite -> b_eq_0 in *.
      rewrite <- H0. simpl. by rewrite <- sndeq.
  - Case "Fun".
    do 2 setoid_rewrite -> SUM_fun_simplx in H4. simpl in H4.
    apply tset_sym in H4. apply PBot_incon_eq in H4. inversion H4.
  - Case "Pair".
    setoid_rewrite -> SUM_fun_simplx in H4. simpl in H4.
    apply tset_sym in H4. apply PBot_incon_eq in H4. inversion H4.
Qed.

Lemma SemVal_FUN_equation2 : forall (E : Env) (η : SemEnv E) (e : Expr E.+2),
    ⟦ λ e ⟧v η =-= inFun (fixp (F ⟦e ⟧e η)).
Proof.
  intros E η e.
  auto.
Qed.

Lemma SemExp_OrdOp_equation :
  forall (E : Env) (η : SemEnv E) (op : OrdOp) (dv dv' : SemEnv E =-> VInf _BOT),
    KR (GenOrdOp (SemOrdOp op) dv dv' η)
    =-=
    KR (GenOrdOp_DInf (SemOrdOp op) dv dv' η).
Proof.
  intros E η op e1 e2.
  simpl. unfold KR.
  repeat rewrite <- comp_simpl.
  repeat rewrite <- comp_assoc.
  assert (forall (f : SemEnv E =-> VInf _BOT),
             kleisli (VInfToNat << Unroll) <<
                     (kleisli (eta << DomainStuff.Roll) << f)
                     =-=
             kleisli VInfToNat << f
         ).
  intros f. rewrite comp_assoc. rewrite <- kleisli_comp2. rewrite <- comp_assoc.
  rewrite UR_id. by rewrite comp_idR.
    by do 2 rewrite H.
Qed.

Lemma SemExp_BoolOp_equation :
  forall (E : Env) (η : SemEnv E) (op : BoolOp) (dv dv' : SemEnv E =-> VInf _BOT),
    KR (GenBoolOp (SemBoolOp op) dv dv' η)
    =-=
    KR (GenBoolOp_DInf (SemBoolOp op) dv dv' η).
Proof.
  intros E η op e1 e2.
  simpl. unfold KR.
  repeat rewrite <- comp_simpl.
  repeat rewrite <- comp_assoc.
  assert (forall (f : SemEnv E =-> VInf _BOT),
             kleisli (VInfToBool << Unroll) <<
                     (kleisli (eta << DomainStuff.Roll) << f)
                     =-=
             kleisli VInfToBool << f
         ).
  intros f. rewrite comp_assoc. rewrite <- kleisli_comp2. rewrite <- comp_assoc.
  rewrite UR_id. by rewrite comp_idR.
    by do 2 rewrite H.
Qed.

Lemma SemExp_NatOp_equation :
  forall (E : Env) (η : SemEnv E) (op : NatOp) (dv dv' : SemEnv E =-> VInf _BOT),
    KR (⦓SemNatOp op ⦔ dv dv' η)
    =-=
    KR (GenNatOp_DInf (SemNatOp op) dv dv' η).
Proof.
  intros E η op e1 e2.
  simpl. unfold KR.
  repeat rewrite <- comp_simpl.
  repeat rewrite <- comp_assoc.
  assert (forall (f : SemEnv E =-> VInf _BOT),
             kleisli (VInfToNat << Unroll) <<
                     (kleisli (eta << DomainStuff.Roll) << f)
                     =-=
             kleisli VInfToNat << f
         ).
  intros f. rewrite comp_assoc. rewrite <- kleisli_comp2. rewrite <- comp_assoc.
  rewrite UR_id. by rewrite comp_idR.
    by do 2 rewrite H.
Qed.

Lemma SemExp_LET_KR_equation :
  forall (E : Env) (e1 : Expr E) (e2 : Expr E.+1),
    (KR << ⟦ LET e1 e2 ⟧e) =-= LetAppDInf ⟦ e2 ⟧e ⟦ e1 ⟧e.
Proof.
  intros E e1 e2. apply fmon_eq_intro.
  intro η. simpl.
  rewrite <- KLEISLIR_KR_eq.
  rewrite <- KLEISLIR_KR_eq2. by simpl.
Qed.

Lemma VInfToNat_Nat : (VInfToNat << inNat) =-= eta.
Proof.
  rewrite comp_assoc. by do 2 setoid_rewrite -> sum_fun_fst.
Qed.

Lemma VInfToFun_Fun : (VInfToFun << inFun) =-= eta.
Proof.
  rewrite comp_assoc. setoid_rewrite -> sum_fun_fst.
    by setoid_rewrite -> sum_fun_snd.
Qed.
