Require Import BOp.
Require Import List.
Require Import ZArith.

(** * Source Language *)

(** Types *)
Inductive type :=
| tunit  : type
| tint   : type             
| tarrow : type -> type -> type
| tpair  : type -> type -> type.

Notation "a ⇾ b" := (tarrow a b) (at level 30, right associativity).
Notation "a ⨱ b"  := (tpair a b)  (at level 30, right associativity).

Definition ctx := list type.

(** Variables *)
(** @see: Benton's strongly typed representation of variables. 
http://research.microsoft.com/en-us/um/people/nick/typedsyntax.pdf *)

Inductive var : ctx -> type -> Type :=
| zvar : forall c θ, var (θ :: c) θ
| svar : forall c θ1 θ2, var c θ1 -> var (θ2 :: c) θ1.

(** Terms *)
Inductive term (c : ctx) : type -> Type :=
| term_unit   : term c tunit
| term_int    : Z -> term c tint
| term_var    : forall θ, var c θ -> term c θ
| term_abs    : forall θ1 θ2, term (θ1 :: c) θ2 -> term c (θ1 ⇾ θ2)
| term_app    : forall θ1 θ2, term c (θ1 ⇾ θ2) -> var c θ1 -> term c θ2
| term_let    : forall θ1 θ2, term (θ1 :: c) θ1 -> term (θ1 :: c) θ2 -> term c θ2
| term_bop    : BOp -> term c tint -> term c tint -> term c tint
| term_ifz    : forall θ, term c tint -> term c θ -> term c θ -> term c θ
| term_pair   : forall θ1 θ2, term c θ1 -> term c θ2 -> term c (θ1 ⨱ θ2)
| term_fst    : forall θ1 θ2, var c (θ1 ⨱ θ2) -> term c θ1
| term_snd    : forall θ1 θ2, var c (θ1 ⨱ θ2) -> term c θ2
.
