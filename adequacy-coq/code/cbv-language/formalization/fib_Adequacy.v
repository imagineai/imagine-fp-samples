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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.

Section Fib_Adequacy.
Variable n : nat_cpoType.

(* The definition of "fib n" in our programming language. *)
Section Fib_Lang.

Definition v0 {E:Env} := ZVAR E.
Definition v1 {E:Env} := SVAR (ZVAR E).
Definition v2 {E:Env} := SVAR (SVAR (ZVAR E)).
Definition v3 {E:Env} := SVAR (SVAR (SVAR (ZVAR E))).
Definition V_v0 {E:Env} := VAL (VAR (@v0 E)).
Definition V_v1 {E:Env} := VAL (VAR (@v1 E)).
Definition V_v2 {E:Env} := VAL (VAR (@v2 E)).
Definition V_v3 {E:Env} := VAL (VAR (@v3 E)).
Definition V_Zero {E:Env} := VAL (@NAT E 0).
Definition V_One {E:Env} := VAL (@NAT E 1).
Definition V_Two {E:Env} := VAL (@NAT E 2).
Definition V0_eq_0 {E:Env} := OOp EqOP (@V_v0 E) V_Zero.
Definition V0_eq_1 {E:Env} := OOp EqOP (@V_v0 E) V_One.

Definition Fib_body {E:Env} := LET (NOp MinusOP V_v0 V_One)
                                  (LET (NOp MinusOP V_v1 V_Two)
                                       (NOp PlusOP
                                            ((VAR (@v3 E)) @ (VAR v0))
                                            ((VAR (@v3 E)) @ (VAR v1))
                                       )
                                  ).

Definition V_Fib {E:Env} := λ (IFB V0_eq_0
                                  V_Zero
                                  (IFB V0_eq_1
                                       V_One
                                       (@Fib_body E)
                                  )
                             ).

Lemma fib_body : ((nat̂ × (nat̂ ⇥ nat̂) × []) e⊢ Fib_body ⦂ nat̂).
Proof.
  eapply LetRule.
  apply NOpRule.
  apply ValRule;apply VarRule.
  apply ValRule;apply NatRule.
  eapply LetRule.
  apply NOpRule.
  apply ValRule;apply VarRule.
  apply ValRule;apply NatRule.
  apply NOpRule.
  apply AppRule with (θ':=nat̂).
  apply VarRule. apply VarRule.
  apply AppRule with (θ':=nat̂).
  apply VarRule. apply VarRule.
Defined.
 
Lemma fib : ([] v⊢ V_Fib ⦂ nat̂ ⇥ nat̂).
Proof.
  apply FunRule.
  apply IfBRule.
  apply OOpRule.
  apply ValRule; apply VarRule.
  apply ValRule; apply NatRule.
  apply ValRule; apply NatRule.  
  apply IfBRule.
  apply OOpRule.
  apply ValRule;apply VarRule.
  apply ValRule;apply NatRule.
  apply ValRule;apply NatRule.
  apply fib_body.
Defined.

Definition fibn_syn : ([] e⊢ V_Fib @ (NAT n) ⦂ nat̂).
Proof.
  apply AppRule with (θ':=nat̂).
  apply fib.
  apply NatRule.
Defined.

End Fib_Lang.

(* Semantic definition of "fib n" *)
Section Fib_Sem.

Lemma strong_induction :
  forall P : nat -> Prop, P 0 -> (forall n, (forall m, (m <= n)%coq_nat -> P m) -> P n.+1) ->
               forall n, P n.
Admitted. (* Strong induction *)
  
Fixpoint coq_fib (m : nat) : nat :=
  match m with
  | 0    => 0
  | S m' => match m' with
           | 0     => 1
           | S m'' => (coq_fib m'' + coq_fib m')%coq_nat
           end
  end
.

Lemma coq_fib_prop : forall x, coq_fib x.+2 = (coq_fib x + coq_fib x.+1)%coq_nat.
Proof. auto. Qed.

Lemma coq_fib_prop2 : forall x,
    coq_fib x.+2 = SemNatOp PlusOP (coq_fib x) (coq_fib x.+1).
Proof. auto. Qed.

Definition fibn_sem := coq_fib n.

Inductive Fib : nat -> nat -> Prop :=
| Fib0 : Fib 0 0
| Fib1 : Fib 1 1
| FibS : forall n m m', Fib n m -> Fib n.+1 m' -> Fib (n.+2) (m + m')%coq_nat
.

Lemma FibCorr : forall m, Fib m (coq_fib m).
Proof.
  apply strong_induction with (P:=fun n => Fib n (coq_fib n)).
  constructor.
  intros n0 H.
  destruct n0.
  constructor.
  rewrite coq_fib_prop.
  constructor.
  apply H. auto.
  apply H. auto.
Qed.

End Fib_Sem.

Lemma fibn_prop : forall n,
  PAIR (SemType nat̂)
       ((PAIR (SemType (nat̂) ⇥ (nat̂)) ())
          (t⟦fib ⟧v ())) n =-=
  PAIR (SemType nat̂)
       ((PAIR (SemType (nat̂) ⇥ (nat̂)) ())
            (fixp
               (exp_fun
                  t⟦IfBRule
                      (OOpRule EqOP (ValRule
                               (VarRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v0))
                               (ValRule
                               (NatRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) 0)))
                      (ValRule (NatRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) 0))
                      (IfBRule
                         (OOpRule EqOP ((ValRule
                               (VarRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v0)))
                               (ValRule
                               (NatRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) 1)))
                         (ValRule (NatRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) 1))
                         fib_body) ⟧e << PAIR (SemType (nat̂) ⇥ (nat̂)) ())))
        n.
Proof. auto. Qed.

Lemma fibn_eq : t⟦ fibn_syn ⟧e () =-= eta fibn_sem.
Proof.
  unfold fibn_syn, fibn_sem.
  apply strong_induction
  with (P:=fun n => t⟦AppRule fib (NatRule [] n) ⟧e () =-= ↑⊥(coq_fib n)).
  - Case "n = 0".
    rewrite -> AppRule_simpl.
    rewrite -> NatRule_simpl.
    unfold fib.
    rewrite FunRule_simpl.
    rewrite fixp_eq.
    rewrite comp_simpl.
    rewrite -> (fst (IfZRule_simpl
                      (OOpRule EqOP (ValRule
                               (VarRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v0))
                               (ValRule
                               (NatRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) 0)))
                      _ _ _)).
      by simpl.
      simpl. rewrite Smash_ValVal. rewrite kleisliVal. by simpl.
  intros m H.
  destruct m.    
  - Case "n = 1".
    rewrite -> AppRule_simpl.
    rewrite -> NatRule_simpl.
    rewrite FunRule_simpl.
    rewrite fixp_eq.
    rewrite comp_simpl.
    rewrite -> (snd (IfZRule_simpl
                      (OOpRule EqOP (ValRule
                               (VarRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v0))
                               (ValRule
                               (NatRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) 0)))
                      _ _ _)).
    rewrite -> (fst (IfZRule_simpl
                      (OOpRule EqOP (ValRule
                               (VarRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v0))
                               (ValRule
                               (NatRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) 1)))
                      _ _ _)).
      by simpl.
    rewrite OOpRule_simpl. simpl. rewrite Smash_ValVal. rewrite kleisliVal.
        by simpl.
    simpl. rewrite Smash_ValVal. rewrite kleisliVal.
      by simpl.
  - Case "n >= 2".
    rewrite coq_fib_prop2.
    rewrite -> AppRule_simpl.
    rewrite -> NatRule_simpl.
    unfold fib.
    rewrite FunRule_simpl.
    rewrite fixp_eq.
    rewrite comp_simpl.
    rewrite <- fibn_prop.
    rewrite -> (snd (IfZRule_simpl
                      (OOpRule EqOP (ValRule
                               (VarRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v0))
                               (ValRule
                               (NatRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) 0)))
                      _ _ _)).
    rewrite -> (snd (IfZRule_simpl
                      (OOpRule EqOP (ValRule
                               (VarRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v0))
                               (ValRule
                               (NatRule (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) 1)))
                      _ _ _)).
    rewrite LetRule_simpl.
    rewrite NOpRule_simpl.
    repeat rewrite ValRule_simpl.
    rewrite Operator2_simpl. rewrite kleisliVal.
    rewrite KLEISLIR_unit2.
    rewrite -> NatRule_simpl.
    rewrite -> VarRule_simpl with (v:=v0).
    simpl ((lookupV (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v0) _).
    assert ((SimpleBOp (SemNatOp MinusOP)) (m.+2, 1) = m.+1) by auto.
    setoid_rewrite -> H0; clear H0.
    rewrite -> LetRule_simpl with (tje:=(NOpRule MinusOP
          (ValRule (VarRule (nat̂) × (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v1))
          (ValRule (NatRule (nat̂) × (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) 2)))).
    repeat rewrite NOpRule_simpl.    
    repeat rewrite ValRule_simpl.
    repeat rewrite -> NatRule_simpl.
    rewrite Operator2_simpl. rewrite kleisliVal.
    rewrite KLEISLIR_unit2.
    rewrite -> VarRule_simpl with (v:=v1).
    simpl ((lookupV (nat̂) × (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v1) _).
    assert ((SimpleBOp (SemNatOp MinusOP)) (m.+2, 2) = m).
    simpl. induction m. by simpl. by simpl.
    setoid_rewrite -> H0; clear H0.
    rewrite -> NOpRule_simpl
    with (op:=PlusOP)
         (tje:=(AppRule
              (VarRule (nat̂) × (nat̂) × (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v3)
              (VarRule (nat̂) × (nat̂) × (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v0)))
    .
    rewrite -> AppRule_simpl.
    rewrite -> VarRule_simpl with (v:=v0).
    simpl ((lookupV (nat̂) × (nat̂) × (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v0) _).
    assert (t⟦VarRule (nat̂) × (nat̂) × (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v3 ⟧v
            ((PAIR (SemType nat̂)
                ((PAIR (SemType (nat̂) ⇥ (nat̂)) ()) (t⟦fib ⟧v ()))) m.+2, m.+1,
             m) =-= (t⟦fib ⟧v ())). auto.
    rewrite -> AppRule_simpl.
    setoid_rewrite -> H0; clear H0.
    rewrite -> VarRule_simpl with (v:=v1).
    simpl ((lookupV (nat̂) × (nat̂) × (nat̂) × ((nat̂) ⇥ (nat̂)) × ([]) v1) _).
    assert (H':=H).
    specialize (H m (Le.le_n_Sn m)).
    specialize (H' m.+1 (Le.le_refl m.+1)).
    rewrite -> AppRule_simpl, -> NatRule_simpl in H.
    rewrite -> AppRule_simpl, -> NatRule_simpl in H'.
    rewrite -> H, -> H'.
    rewrite Operator2_simpl. rewrite kleisliVal. apply tset_refl.
    rewrite OOpRule_simpl. simpl.
    rewrite Operator2_simpl. rewrite kleisliVal. apply tset_refl.
    rewrite OOpRule_simpl. simpl.
    rewrite Operator2_simpl. rewrite kleisliVal. apply tset_refl.
Qed.

Definition a_fibn := Eval hnf in (Adequacy1_n (tj:=fibn_syn) fibn_eq).

End Fib_Adequacy.
