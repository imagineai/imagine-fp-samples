(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *) 

Add LoadPath "../domain-theory".
Add LoadPath "../extended-cbn".

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Utils.
Require Import Program.

Require Import Lang.
Require Import Types.
Require Import InSem.
Require Import ExSem.
Require Import DomainStuff.
Require Import OperSem.

Require Import Relations.Relation_Operators.
Require Import Adequacy.

Require Import PredomAll.
Require Import Domains.

Require Import MoT.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.

Definition V_True {E:Env} := @BOOL E true.
Definition V_False {E:Env} := @BOOL E false.
Definition E_True {E:Env} := @VAL E V_True.
Definition E_False {E:Env} := @VAL E V_False.
Definition v0 {E:Env} := ZVAR E.
Definition v1 {E:Env} := SVAR (ZVAR E).
Definition v2 {E:Env} := SVAR (SVAR (ZVAR E)).
Definition v3 {E:Env} := SVAR (SVAR (SVAR (ZVAR E))).
Definition V_v0 {E:Env} := VAL (VAR (@v0 E)).
Definition V_v1 {E:Env} := VAL (VAR (@v1 E)).
Definition V_v2 {E:Env} := VAL (VAR (@v2 E)).
Definition V_v3 {E:Env} := VAL (VAR (@v3 E)).

Definition bool_sum {E:Env} := FUN (VAL (FUN (@NOp (E.+4) PlusOP V_v0 V_v2))).

Definition bool_sum_app {E:Env} :=
  LET (APP (@bool_sum E) V_True)
      (APP (VAR v0) V_False)
.

Lemma bool_sum_tj : ([] v⊢ bool_sum ⦂ nat̂ ⇥ nat̂ ⇥ nat̂).
Proof.
  apply FunRule.
  apply ValRule.
  apply FunRule.
  apply NOpRule.
  apply ValRule. apply VarRule.
  apply ValRule. apply VarRule.
Qed.

Lemma bool_sum_tj' : ([] v⊢ bool_sum ⦂ bool̂ ⇥ bool̂ ⇥ nat̂).
  apply SubsVRule with (θ:=nat̂ ⇥ nat̂ ⇥ nat̂).
  apply bool_sum_tj.
  apply SubFunRule. constructor.
  apply SubFunRule. constructor.
  constructor.
Qed.

(* Tipamos True y False a nat̂ *)
Lemma bool_sum_app_tj : ([] e⊢ bool_sum_app ⦂ nat̂).
Proof.
  apply LetRule with (θ':=nat̂ ⇥ nat̂).
  apply AppRule with (θ':=nat̂).
  apply bool_sum_tj.
  apply SubsVRule with (θ:=bool̂). constructor. constructor.
  apply AppRule with (θ':=nat̂).
  apply VarRule.
  apply SubsVRule with (θ:=bool̂). constructor. constructor.
Qed.

(* Tipamos la suma como + : bool̂ ⇥ bool̂ ⇥ nat̂ *)
Lemma bool_sum_app_tj' : ([] e⊢ bool_sum_app ⦂ nat̂).
Proof.
  apply LetRule with (θ':=bool̂ ⇥ nat̂).
  apply AppRule with (θ':=bool̂).
  apply bool_sum_tj'. constructor.
  apply AppRule with (θ':=bool̂).
  apply VarRule. constructor.
Qed.

Lemma bool_sum_coherent :
  t⟦ bool_sum_app_tj ⟧e () =-= t⟦ bool_sum_app_tj' ⟧e ()
.
Proof.
  apply Coherence.
Qed.

Definition true_sum_false {E:Env} := @NOp E PlusOP (VAL V_True) (VAL V_False).

Lemma true_sum_computes : (∅, true_sum_false) ⟼⋆ (∅, ⌊ 1 ⌋).
Proof.
  eapply rt_trans. eapply rt_step.
  constructor.
  eapply rt_trans. eapply rt_step.
  constructor.
  eapply rt_trans. eapply rt_step.
  constructor.
  eapply rt_trans. eapply rt_step.
  constructor.
  eapply rt_trans. eapply rt_step.
  constructor.
  apply rt_refl.
Qed.
