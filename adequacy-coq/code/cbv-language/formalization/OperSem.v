
(*begin hide*)
Require Import Utils.
Require Import Lang.

Require Import Relations.Relation_Definitions.
Require Import Relations.Relation_Operators.
(*end hide*)

(** *)
(*** Chapter 4: Extended Language Definition ***)
(** *)

Definition Op_B_to_N (b : bool) : nat :=
  match b with
  | true => 1
  | false => 0
  end.

(** *Definition 38: Operational rules *)

Reserved Notation "A ⟼ B" (at level 1, no associativity).

Inductive SemOper : (FS * Expr 0) -> (FS * Expr 0) -> Prop :=
| SLet  : forall E e e'   , (E, LET e e')                ⟼ (E ⊚ e', e)
| App   : forall E e v    , (E, ((λ e) @ v))             ⟼ (E, e⎩[v,(λ e)]⎭)
| SOOp  : forall E op e e', (E, OOp op e e') ⟼ (PUSHLOOp op E e', e)
| DOOp : forall E op n m  , (PUSHROOp op E ⌊ n ⌋, ⌊ m ⌋) ⟼ (E, ⎣ SemOrdOp op n m ⎦)
| IOOp : forall E op e n  , (PUSHLOOp op E e, ⌊ n ⌋)  ⟼ (PUSHROOp op E ⌊ n ⌋ ,e)
| SBOp  : forall E op e e', (E, BOp op e e') ⟼ (PUSHLBOp op E e', e)
| DBOp : forall E op b b' , (PUSHRBOp op E ⎣ b ⎦, ⎣ b' ⎦) ⟼ (E, ⎣ SemBoolOp op b b' ⎦)
| IBOp : forall E op e b  , (PUSHLBOp op E e, ⎣ b ⎦)  ⟼ (PUSHRBOp op E ⎣ b ⎦ ,e)
| SNOp  : forall E op e e', (E, NOp op e e')             ⟼ (E ∘ ( ⊡ ⦓ op ⦔ e' ), e)
| DNOp : forall E op n m  , (E ∘ ( ⌊ n ⌋ ⦓ op ⦔ ⊡ ), ⌊ m ⌋) ⟼ (E, ⌊ SemNatOp op n m ⌋)
| INOp : forall E op e n  , (E ∘ ( ⊡ ⦓ op ⦔ e ), ⌊ n ⌋)  ⟼ (E ∘ ( ⌊ n ⌋ ⦓ op ⦔ ⊡ ),e)
| Subst : forall E v e'   , (E ⊚ e', VAL v)              ⟼ (E, e' ⎩[v]⎭)
| IfB   : forall E eb e e', (E, IFB eb e e')             ⟼ (E ∘ ( e ⇆ e' ), eb)
| IfBT   : forall E e e'  , (E ∘ ( e ⇆ e' ), VAL (BOOL true))  ⟼ (E, e)
| IfBF   : forall E e e'  , (E ∘ ( e ⇆ e' ), VAL (BOOL false)) ⟼ (E, e')
| FstOp  : forall E v v',   (E, EFST (VPAIR v v'))       ⟼ (E, VAL v)
| SndOp  : forall E v v',   (E, ESND (VPAIR v v'))       ⟼ (E, VAL v')
| BoolCast : forall E b,   (E, VAL (BOOL b))       ⟼ (E, VAL (NAT (Op_B_to_N b)))
where "A ⟼ B" := (SemOper A B).

(** Reflexive and transitive closure of the reduction relation *)
Definition SemOperStar : relation (FS * Expr 0) :=
  clos_refl_trans (FS * Expr 0) SemOper.

Infix "⟼⋆" := SemOperStar (at level 1, no associativity).

(** n-step reduction *)
Inductive SemOperStep : nat -> (FS * Expr 0) -> Prop :=
| Z_Step : forall fs e, SemOperStep 0 (fs, e)
| S_Step : forall n fs e fs' e', SemOperStep n (fs', e') ->
                            ((fs,e) ⟼ (fs',e')) ->
                            SemOperStep n.+1 (fs, e)
.

(** Divergent reduction *)
Definition SemOperDiverge (fse : FS * Expr 0) := forall n, SemOperStep n fse.

(* Properties *)
Lemma closed_transition : forall (E E' : FS) (v : V 0) (e' : Expr 0),
    (E, VAL v) ⟼ (E', e') -> (exists b, v = BOOL b) \/
                              (exists m, v = NAT m) \/
                              (exists f, v = λ f)   \/
                              (exists v' v'', v = VPAIR v' v'').
Proof.
  intros E E' v e' H.
  destruct v.
  - Case "v = VAR".
    inversion v.
  - Case "v = BOOL".
    left. by exists b.
  - Case "v = NAT".
    right. left. by exists n.
  - Case "v = FUN".
    right. right. left. by exists e.
  - Case "v = PAIR".
    right. right. right. by exists v1, v2.
Qed.

Lemma closed_star_transition : forall (E E' : FS) (v : V 0) (e' : Expr 0),
    (E, VAL v) ⟼⋆ (E', e') -> (exists b, v = BOOL b) \/
                               (exists m, v = NAT m) \/
                               (exists f, v = λ f)   \/
                               (exists v' v'', v = VPAIR v' v'').
Proof.
  intros E E' v e' H.
  destruct v.
  - Case "v = VAR".
    inversion v.
  - Case "v = BOOL".
    left. by exists b.
  - Case "v = NAT".
    right. left. by exists n.
  - Case "v = FUN".
    right. right. left. by exists e.
  - Case "v = PAIR".
    right. right. right. by exists v1, v2.
Qed.
