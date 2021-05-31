Add Rec LoadPath "." as Top.
Set Automatic Coercions Import.
Set Implicit Arguments.

Require Import Syntax.
Require Import Machine.

(** * Translations from source to target language *)

(** Translate source vars into numbers (the corresponding De Bruijn index) *)
Fixpoint var_to_nat ctx a (v : var ctx a) : nat :=
  match v with
    zvar _ _ => 0
  | svar _ _ _ v => S (var_to_nat v)
  end.

(** Translate terms into machine instructions *)
Fixpoint compile ctx a (t : term ctx a) : Code :=
  match t with
  | term_unit _           => ival iunit
  | term_int _ n          => ival (iint n)
  | term_var _ _ v        => iaccess (var_to_nat v)
  | term_abs _ _ _ t      => ival (igrab (compile  t))
  | term_app _ _ _ t v    => ipush (var_to_nat v) (compile t)
  | term_let _ _ _ t1 t2  => ilet (irec (compile t1)) (compile t2)
  | term_bop _ bop t1 t2  => ibop bop (compile t1) (compile t2)
  | term_ifz _ _ t1 t2 t3 => iifz (compile t1) (compile t2) (compile t3)
  | term_pair _ _ _ t1 t2 => ival (ipair (compile t1) (compile t2))
  | term_fst _ _ _ v      => ifst (var_to_nat v)
  | term_snd _ _ _ v      => isnd (var_to_nat v)
  end.

Notation "⦇ t ⦈" := (compile t) (at level 70, no associativity).

(** Lookup a variable at the context and return the corresponding type *)
Lemma nth_var_to_nat:
  forall ctx a, forall v : var ctx a,  nth_error ctx (var_to_nat v) = Some a.
Proof.
  induction v.
  simpl. auto.
  simpl. auto.
Qed.
