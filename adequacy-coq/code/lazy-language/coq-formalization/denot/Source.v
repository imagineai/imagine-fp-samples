(** * Source : The Source language *)
Add LoadPath "./domain-theory".
Set Automatic Coercions Import.
Require Import Arith.
Require Import Util.
Require Import Common.
Require Import Operator.
Require Import VecList.
Require Import Vector.
Set Implicit Arguments.
Unset Strict Implicit.

(** Types and contexts *)
Inductive type :=
  | ty_int : type
  | ty_arrow : type -> type -> type
  | ty_prod : type -> type -> type.

Notation "θ ⇾ θ'" := (ty_arrow θ θ') 
(at level 30, right associativity).

Notation "θ × θ'" := (ty_prod θ θ')
(at level 20, right associativity).

Definition context := list type.

(** Typed Terms *)
Inductive term (ctx : context) : type -> Type :=
| term_abs: forall θ θ', term (θ :: ctx) θ' -> term ctx (θ ⇾ θ')
| term_app: forall θ θ', term ctx (θ ⇾ θ') -> term ctx θ -> term ctx θ'
| term_var: forall n θ, lookup ctx n = Some θ -> term ctx θ
| term_fix: forall θ, term ctx (θ ⇾ θ) -> term ctx θ
| term_const: nat -> term ctx ty_int
| term_op: 
    forall n (op : operator (S n)), 
      Vector.t (term ctx ty_int) (S n)  ->
      term ctx ty_int
| term_pair: forall θ θ', term ctx θ -> term ctx θ' -> term ctx (θ × θ')
| term_fst: forall θ θ', term ctx (θ × θ') -> term ctx θ
| term_snd: forall θ θ', term ctx (θ × θ') -> term ctx θ'
| term_cond: forall θ, term ctx ty_int -> term ctx (θ × θ) -> term ctx θ.

(** An induction principle that provides inductive hypotheses for operator
arguments *)
Definition term_ind2 (P : forall ctx t, term ctx t -> Prop) 
(fabs : forall ctx a b t,  P (a :: ctx) b t -> P ctx (a ⇾ b) (term_abs t))
(fapp : forall ctx a b t1 t2, 
          P ctx (a ⇾ b) t1 -> P ctx a t2 -> P ctx b (term_app t1 t2))
(fvar : forall ctx n a (H : lookup ctx n = Some a), P ctx a (term_var H))
(ffix : forall ctx a t, P ctx (a ⇾ a) t -> P ctx a (term_fix t))
(fcons : forall ctx m, P ctx ty_int (term_const ctx m))
(fop : forall ctx n (op : operator (S n)) (v : Vector.t (term ctx ty_int) (S n)),
              Forall (P ctx ty_int) v -> P ctx ty_int (term_op op v))
(fpair : forall ctx a b t1 t2, 
           P ctx a t1 -> P ctx b t2 -> P ctx (a × b) (term_pair t1 t2))
(ffst : forall ctx a b t, P ctx (a × b) t -> P ctx a (term_fst t))
(fsnd : forall ctx a b t, P ctx (a × b) t -> P ctx b (term_snd t))
(fcond : forall ctx a ti tp, 
           P ctx ty_int ti -> P ctx (a × a) tp -> P ctx a (term_cond ti tp))
: forall ctx a t,  P ctx a t :=
fix F (ctx : context) (a : type) (t : term ctx a) {struct t} : P ctx a t :=
  match t in (term _ a0) return P ctx a0 t with
      term_abs a b t1 => fabs _ _ _ _ (F _ _ t1)
    | term_app a b t1 t2 => fapp ctx a b t1 t2 (F _ _ t1) (F _ _ t2)
    | term_var b a H => fvar _ _ _ H
    | term_fix a t' => ffix _ _ _ (F _ _ t')
    | term_const m => fcons _ m
    | term_op n op args => 
      let G := 
          fix G n (v : Vector.t (term ctx ty_int) n) {struct v} : 
                 Forall (P ctx ty_int) v := 
              match v return Forall (P ctx ty_int) v with
                  nil => Forall_nil _
                | Vector.cons t' _ v0 => Forall_cons _ _ _ (F _ _ t') (G _ v0)
              end
      in
      fop _ _ _ args (G _ args)
    | term_pair a b t1 t2 => fpair ctx a b t1 t2 (F _ _ t1) (F _ _ t2)
    | term_fst a b t1 => ffst ctx a b t1 (F _ _ t1)
    | term_snd a b t1 => fsnd ctx a b t1 (F _ _ t1)
    | term_cond a ti tp => fcond ctx a ti tp (F _ _ ti) (F _ _ tp)
  end.

