(** printing e⊢ #e&vdash;# *) (** printing ⦂ #&colon;# *)
(*begin hide*)
Add LoadPath "../domain-theory".
Require Import Utils.
Require Import Program.
Require Import Coq.Vectors.Vector.

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

Require Import Lang.

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Domains.
Require Import DomainStuff.
Include RD.
Require Import PredomLift.
(*end hide*)

(** *)
(*** Chapter 4: Extended Language Type System ***)
(** *)

(** *Definition 3.5: Types and contexts *)
Inductive LType :=
| BoolTy  : LType
| NatTy  : LType
| FunTy  : LType -> LType -> LType
| PairTy : LType -> LType -> LType
.

Definition LCtx (E : Env) := t LType E.

(** *Notation *)
Notation "'bool̂'" := (BoolTy) (at level 1, no associativity).
Notation "'nat̂'" := (NatTy) (at level 1, no associativity).
Infix "⇥" := (FunTy) (at level 0, right associativity).
Infix "⨱" := (PairTy) (at level 0, right associativity).

Notation "'[]'" := (nil LType) (at level 1, no associativity).
Notation "θ × Γ" := (@cons LType θ _ Γ) (at level 0, right associativity).

Reserved Notation "Γ 'v⊢' v ⦂ θ" (at level 201, no associativity).
Reserved Notation "Γ 'e⊢' e ⦂ θ" (at level 201, no associativity).
Reserved Notation "θ1 't≤' θ2" (at level 202, no associativity).
Reserved Notation "'t⟦' tjl '⟧l'" (at level 1, no associativity).

Inductive TypeJudgeL : LType -> LType -> Type :=
| BoolToNatRule : TypeJudgeL BoolTy NatTy
| ReflRule      : forall θ, (θ t≤ θ)
| TransRule     : forall θ θ' θ'', (θ t≤ θ') -> (θ' t≤ θ'') ->
                              TypeJudgeL θ θ''
| SubPairRule   : forall θ0 θ0' θ1 θ1', TypeJudgeL θ0 θ0' -> TypeJudgeL θ1 θ1' ->
                                   TypeJudgeL (PairTy θ0 θ1) (PairTy θ0' θ1')
| SubFunRule    : forall θ0 θ0' θ1 θ1', TypeJudgeL θ0' θ0 -> TypeJudgeL θ1 θ1' ->
                                   TypeJudgeL (θ0 ⇥ θ1) (θ0' ⇥ θ1')
where "θ 't≤' θ'" := (TypeJudgeL θ θ').

Definition lookupType  := 
fix nth_fix {E} (Γ : t LType E) (v : Var E) {struct Γ} : LType :=
match v in Var E' return t LType E' -> LType with
 |ZVAR _    => fun Γ' => caseS (fun _ _ => LType) (fun θ n t => θ) Γ'
 |SVAR _ v' => fun Γ' => (caseS (fun E' _ => Var E' -> LType)
                              (fun _ n Γ'' w => nth_fix Γ'' w) Γ') v'
end Γ.

(** *Definition 43: Typing rules *)
Inductive TypeJudgeV : forall (E : Env), LCtx E -> V E -> LType -> Type :=
| BoolRule  : forall (E : Env) (Γ : LCtx E) (b : bool),
             (Γ v⊢ (BOOL b) ⦂ bool̂)
| NatRule  : forall (E : Env) (Γ : LCtx E) (n : nat),
             (Γ v⊢ (NAT n) ⦂ nat̂)
| VarRule  : forall (E : Env) (Γ : LCtx E) (v : Var E),
             (Γ v⊢ (VAR v) ⦂ (lookupType Γ v))
| FunRule  : forall (E : Env) (Γ : LCtx E) (e : Expr E.+2) (θ' θ : LType),
             ((θ' × (θ' ⇥ θ) × Γ) e⊢ e ⦂ θ) ->
             (Γ v⊢ λ e ⦂ (θ' ⇥ θ))
| PairRule  : forall (E : Env) (Γ : LCtx E) (v v' : V E) (θ θ' : LType),
              (Γ v⊢ v ⦂ θ) ->
              (Γ v⊢ v' ⦂ θ') ->
              (Γ v⊢ VPAIR v v' ⦂ θ ⨱ θ')
| SubsVRule : forall (E : Env) (Γ : LCtx E) (v : V E) (θ θ' : LType),
                (Γ v⊢ v ⦂ θ) ->
                TypeJudgeL θ θ' ->
                (Γ v⊢ v ⦂ θ')
with TypeJudgeE : forall (E : Env), LCtx E -> Expr E -> LType -> Type :=
| ValRule : forall (E : Env) (Γ : LCtx E) (v : V E) (θ : LType),
                               (Γ v⊢ v ⦂ θ) -> (Γ e⊢ (VAL v) ⦂ θ)
| OOpRule : forall (E : Env) (Γ : LCtx E) (op : OrdOp) (e e' : Expr E),
                               (Γ e⊢ e ⦂ nat̂) -> (Γ e⊢ e' ⦂ nat̂) ->
                               (Γ e⊢ (OOp op e e') ⦂ bool̂)
| BOpRule : forall (E : Env) (Γ : LCtx E) (op : BoolOp) (e e' : Expr E),
                               (Γ e⊢ e ⦂ bool̂) -> (Γ e⊢ e' ⦂ bool̂) ->
                               (Γ e⊢ (BOp op e e') ⦂ bool̂)
| NOpRule : forall (E : Env) (Γ : LCtx E) (op : NatOp) (e e' : Expr E),
                               (Γ e⊢ e ⦂ nat̂) -> (Γ e⊢ e' ⦂ nat̂) ->
                               (Γ e⊢ (NOp op e e') ⦂ nat̂)
| LetRule  : forall (E : Env) (Γ : LCtx E)
               (e : Expr E) (e' : Expr E.+1) (θ θ' : LType),
                               (Γ e⊢ e ⦂ θ') -> ((θ' × Γ) e⊢ e' ⦂ θ) ->
                               (Γ e⊢ (LET e e') ⦂ θ)
| AppRule : forall (E : Env) (Γ : LCtx E) (v v' : V E) (θ θ' : LType),
                              (Γ v⊢ v ⦂ (θ' ⇥ θ)) -> (Γ v⊢ v' ⦂ θ') ->
                              (Γ e⊢ (v @ v') ⦂ θ)
| IfBRule  : forall (E : Env) (Γ : LCtx E) (e0 e1 e2 : Expr E) (θ : LType),
                               (Γ e⊢ e0 ⦂ bool̂) ->
                               (Γ e⊢ e1 ⦂ θ) ->
                               (Γ e⊢ e2 ⦂ θ) ->
                               (Γ e⊢ IFB e0 e1 e2 ⦂ θ)
| FSTRule  : forall (E : Env) (Γ : LCtx E) (v : V E) (θ θ' : LType),
                               (Γ v⊢ v ⦂ θ ⨱ θ') ->
                               (Γ e⊢ EFST v ⦂ θ)
| SNDRule  : forall (E : Env) (Γ : LCtx E) (v : V E) (θ θ' : LType),
                               (Γ v⊢ v ⦂ θ ⨱ θ') ->
                               (Γ e⊢ ESND v ⦂ θ')
| SubsRule : forall (E : Env) (Γ : LCtx E) (e : Expr E) (θ θ' : LType),
                               (Γ e⊢ e ⦂ θ) ->
                               TypeJudgeL θ θ' ->
                               (Γ e⊢ e ⦂ θ')
where "Γ v⊢ v ⦂ θ" := (TypeJudgeV Γ v θ) and "Γ e⊢ e ⦂ θ" := (TypeJudgeE Γ e θ).

(** *Definition 44: Intrinsic semantics of types *)
Fixpoint SemType (θ : LType) : cpoType :=
  match θ with
  | bool̂ => bool_cpoType
  | nat̂ => nat_cpoType
  | θ ⇥ θ' => (SemType θ) -=> (SemType θ') _BOT
  | θ ⨱ θ' => (SemType θ) * (SemType θ')
  end.

Definition SemBoolToNatRule : bool_cpoType =-> nat_cpoType
  := Fcont_app ((CURRY (@IfB one_cpoType nat_cpoType))
                 ((const one_cpoType 0), (const one_cpoType 1))) ().

Definition SemSubFunRule
           (θ0 θ0' θ1 θ1' : LType)
           (f : SemType θ0' =-> SemType θ0) (g : SemType θ1 =-> SemType θ1') :
  SemType (θ0 ⇥ θ1) =-> SemType (θ0' ⇥ θ1')
  := exp_fun (kleisli (eta << g) << ev << Id >< f).
Arguments SemSubFunRule [θ0 θ0' θ1 θ1'] _ _.

(** *Definition 45: Intrinsic semantics of Subtyping *)
Fixpoint SemTypeJudgeL (θ θ' : LType) (tjl : TypeJudgeL θ θ') :
    SemType θ =-> SemType θ' :=
  match tjl with
  | BoolToNatRule                  => B_to_N
  | ReflRule θ                     => Id (A:=SemType θ)
  | TransRule _ _ _ tjl' tjl''     => SemTypeJudgeL tjl'' << SemTypeJudgeL tjl'
  | SubPairRule _ _ _ _ tjl' tjl'' => SemTypeJudgeL tjl' >< SemTypeJudgeL tjl''
  | SubFunRule _ _ _ _ tjl' tjl''  => SemSubFunRule (SemTypeJudgeL tjl')
                                                   (SemTypeJudgeL tjl'')
  end
where "'t⟦' tjl '⟧l'" := (SemTypeJudgeL tjl).
Arguments SemTypeJudgeL [θ θ'] _.

Fixpoint SemCtx (E : Env) (Γ : LCtx E) : cpoType :=
  match Γ with
  | nil => One
  | cons θ _ Γ => SemCtx Γ * SemType θ
  end.

(** *Functions and Properties *)
Definition lookupV  := 
  fix nth_v {E} (Γ : LCtx E) (v : Var E) {struct Γ} :
    SemCtx Γ =-> SemType (lookupType Γ v) :=
    match v in Var E' return
          forall (Γ' : LCtx E'), SemCtx Γ' =-> SemType (lookupType Γ' v) with
    |ZVAR _    => fun Γ' => caseS (fun E' Γ'' =>
                                 SemCtx Γ'' =-> SemType (lookupType Γ'' (ZVAR _)))
                                (fun θ n t => pi2 (A:= SemCtx t)) Γ'
    |SVAR n v' => fun Γ' => (caseS (fun E' Γ'' => forall (w : Var E'),
                                    SemCtx Γ'' =->
                                           SemType (lookupType Γ'' (SVAR w))))
                                 (fun t n Γ''' w => nth_v Γ''' w << pi1) n Γ' v'
    end Γ.
  