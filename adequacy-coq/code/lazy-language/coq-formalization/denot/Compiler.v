(** * Compiler : Definition of the compiler *)
Add LoadPath "./domain-theory".
Require Import Target.
Require Import Source.
Require Import List.
Require Import Vector.
Require Import VecList.
Require Import Common.
Require Import Operator.
Set Implicit Arguments.

(** * The compilation function *)
(** Compilation of terms into a sequence of intructions *)
Fixpoint compile ctx a (q : term ctx a) {struct q} : Target.code :=
  match q with
    | term_abs _ _ q  => igrab (compile q)
    | term_app _ _ qf qa => ipush (compile qa) (compile qf)
    | term_var n _ _  => iaccess n
    | term_fix _ qf => ifix (compile qf)
    | term_const m => iconst m
    | term_op _ op qargs => 
      fold_right ipush (rmap (@compile _ _) qargs) (iframe _ op)   
    | term_pair _ _ q1 q2 => ipair (compile q1) (compile q2)
    | term_fst _ _ q => ipush ifst (compile q)
    | term_snd _ _ q => ipush isnd (compile q)
    | term_cond _ qi qp => ipush (compile qi) (compile qp)
  end.
(* Here rmap f is equivalent to map f . reverse *)

(** The intended definition for operators *)
(*  Termination checker doesn't allow to define directly in this way *)
Lemma compile_op_fold:
  forall n (op : operator (S n)) ctx (v : t (term ctx ty_int) (S n)),
    compile (term_op op v) 
    = List.fold_right 
        ipush (iframe _ op) 
        (List.map (@compile _ _) (List.rev (to_list v))).
Proof.
  intros n op ctx v.
  simpl.
  rewrite fold_right_lv.
  eapply f_equal.
  rewrite rmap_reverse.
  rewrite <- reverse_tolist.
  eapply to_list_map.
Qed.
  
(** * An alternative compiler of raw terms *)

Inductive rterm : Type :=
| rterm_abs: rterm -> rterm
| rterm_app : rterm -> rterm -> rterm
| rterm_var : var -> rterm
| rterm_fix : rterm -> rterm
| rterm_const : nat -> rterm
| rterm_op : forall n (op : operator (S n)), 
    Vector.t rterm (S n) ->
    rterm
| rterm_pair : rterm -> rterm -> rterm
| rterm_fst : rterm -> rterm
| rterm_snd : rterm -> rterm
| rterm_cond : rterm -> rterm -> rterm.

(** Well-typed terms are associated with a raw term *)
Fixpoint term_rterm ctx a (q : term ctx a) : rterm :=
  match q with
      term_abs _ _ q => rterm_abs (term_rterm q)
    | term_app _ _ q1 q2 => rterm_app (term_rterm q1) (term_rterm q2)
    | term_var n _ _ => rterm_var n
    | term_fix _ q => rterm_fix (term_rterm q)
    | term_const n => rterm_const n
    | term_op n op v => rterm_op op (map (@term_rterm ctx ty_int) v)
    | term_pair _ _ q0 q1 => rterm_pair (term_rterm q0) (term_rterm q1)
    | term_fst _ _ q0 => rterm_fst (term_rterm q0)
    | term_snd _ _ q0 => rterm_snd (term_rterm q0)
    | term_cond _ q0 q1 => rterm_cond (term_rterm q0) (term_rterm q1)
  end.

(** Untyped compiler *)
Fixpoint rcompile (r : rterm) : Target.code :=
  match r with
      rterm_abs t0 => igrab (rcompile t0)
    | rterm_app t1 t2 => ipush (rcompile t2) (rcompile t1)
    | rterm_var n => iaccess n
    | rterm_fix t0 => ifix (rcompile t0)
    | rterm_const m => iconst m
    | rterm_op n op v => fold_right ipush (rmap rcompile v) (iframe _ op)
    | rterm_pair t1 t2 => ipair (rcompile t1) (rcompile t2)
    | rterm_fst t0 => ipush ifst (rcompile t0)
    | rterm_snd t0 => ipush isnd (rcompile t0)
    | rterm_cond t1 t2 => ipush (rcompile t1) (rcompile t2)
  end.

(** Compilation of operators *)
Lemma rcompile_op_fold:
  forall n (op : operator (S n)) (v : t rterm (S n)),
    rcompile (rterm_op op v) 
    = List.fold_right 
        ipush (iframe _ op) 
        (List.map rcompile (List.rev (to_list v))).
Proof.
  intros n op v.
  simpl.
  rewrite fold_right_lv.
  eapply f_equal.
  rewrite rmap_reverse.
  rewrite <- reverse_tolist.
  eapply to_list_map.
Qed.

Ltac rewrite_and_clear :=
  match goal with
      | [H : _ = _ |- _] => rewrite H; clear H
  end.

(** The typed and untyped compilers are essentially the same *)
Lemma compile_rcompile :
  forall ctx a (q : term ctx a),
    compile q = rcompile (term_rterm q).
Proof.
  intros ctx a q.
  set (P ctx a q := @compile ctx a q = rcompile (term_rterm q)).
  fold (P ctx a q).
  generalize ctx a q.
  clear ctx a q.
  eapply term_ind2 ;
  intros ;
  unfold P in * ;
  try (
      simpl ;
      repeat rewrite_and_clear ;
      auto ; 
      fail
  ).
  unfold term_rterm.
  fold (@term_rterm ctx ty_int).
  rewrite compile_op_fold.
  rewrite rcompile_op_fold.
  set (i := iframe (S n) op).
  generalize i.
  clear i.
  generalize n v H.
  clear.
  induction 1 ;
  intro i.
  simpl. auto.
  unfold to_list at 1.
  fold (to_list v).
  unfold map.
  fold (map (@term_rterm ctx ty_int) v).
  unfold to_list at 2.
  fold (to_list (map (@term_rterm ctx ty_int) v)).
  unfold List.rev at 1.
  fold (List.rev (to_list v)).
  unfold List.rev at 2.
  fold (List.rev (to_list (map (@term_rterm ctx ty_int) v))).
  repeat rewrite map_app.
  repeat rewrite fold_right_app.
  simpl.
  rewrite H.
  eauto.
Qed.  
