(** * VecList : Some helpers about lists and vectors *)
Require Export List.
Require Import Arith.
Require Import Vector.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep_dec.
Set Implicit Arguments.
Import VectorDef.VectorNotations.
Open Scope vector_scope.
Delimit Scope vector_scope with V.

(* Since the Vector lib is too short and has too few lemmas,
   we use List definitions instead *)

(** [to_list] *) 
Lemma to_list_of_list:
  forall A (l : list A),
    to_list (of_list l) = l.
Proof.
  intros A. induction l.
  simpl.
  auto.
  simpl.
  unfold to_list.
  fold (to_list (of_list l)).
  rewrite IHl.
  reflexivity.
Qed.

Lemma to_list_length A n (xs : t A n) :
  length (to_list xs) = n.
Proof.
  induction n ;
  dependent destruction xs.
  simpl. auto.
  unfold to_list.
  simpl.
  eapply f_equal.
  eapply IHn.
Qed.

Lemma to_list_append:
  forall A n m (xs : t A n) (ys : t A m),
    to_list (append xs ys) = to_list xs ++ to_list ys.
Proof.
  induction n as [n | n Hip];
  intros m xs ys ;
  dependent destruction xs.
  simpl. auto.
  unfold to_list at 1.
  simpl.
  fold (to_list xs).
  fold (to_list (append xs ys)).
  pattern (to_list (append xs ys)).
  pattern (to_list xs ++ to_list ys).
  eapply f_equal.
  eauto.
Qed.

Lemma to_list_shiftin:
  forall A n x (xs : t A n),
    to_list (shiftin x xs) = to_list xs ++ (x :: List.nil).
Proof.
  induction n as [ | n Hip] ;
  intros x xs ;
  dependent destruction xs.
  simpl.
  reflexivity.
  simpl.
  fold (to_list xs).
  unfold to_list at 1.
  eapply f_equal.
  eapply Hip.
Qed.

Lemma to_list_map:
  forall A B (f : A -> B) n (xs : t A n),
    to_list (map f xs) = List.map f (to_list xs).
Proof.
  intros A B f.
  induction n ;
  intros xs ;
  dependent destruction xs.
  simpl. auto.
  simpl. 
  unfold to_list.
  fold (to_list xs).
  fold (to_list (map f xs)).
  eapply f_equal.
  eauto.
Qed.

Lemma to_list_inj:
  forall A n (xs : t A n) (ys : t A n),
    to_list xs = to_list ys ->
    xs = ys.
Proof.
  induction n.
  intros xs ys.
  dependent destruction xs.
  dependent destruction ys.
  trivial.
  intros xs ys.
  dependent destruction xs.
  dependent destruction ys.
  intros Q0.
  unfold to_list in Q0. 
  fold (to_list xs) in Q0.
  fold (to_list ys) in Q0.
  injection Q0.
  intros.
  specialize (IHn xs ys).
  rewrite IHn. subst.
  auto. auto.
Qed.

(** [shiftin] *)

Lemma shiftin_map:
  forall (A B : Type) (f : A -> B) n, 
  forall (xs : t A n),
  forall (x : A),
    map f (shiftin x xs) = shiftin (f x) (map f xs).
Proof.
  intros A B f.
  induction n ;
  intros xs x ;
  dependent destruction xs ;
  simpl.
  reflexivity.
  rewrite IHn.
  reflexivity.
Qed.

(** [reverse] *)
(* the Vector.rev function is unusable :S, we define it in a different way:  *)
Fixpoint reverse A n (v : t A n) : t A n :=
  match v in t _ n0 return t A n0 with
      | nil _ => nil _
      | x :: v' => shiftin x (reverse v')
  end.

Lemma reverse_nil A : reverse ([] : t A 0) = [].
Proof. 
trivial.
Qed.

Lemma reverse_cons A n x (xs : t A n) : 
  reverse (x :: xs) = shiftin x (reverse xs).
Proof. 
trivial.
Qed.
  
Lemma reverse_tolist A n (xs : t A n):
  to_list (reverse xs) = List.rev (to_list xs).
Proof.
  induction n ;
  dependent destruction xs ;
  simpl ;
  auto.
  rewrite to_list_shiftin.
  rewrite IHn.
  auto.
Qed.

Lemma reverse_lv:
  forall A n (xs : t A n),
    to_list (reverse xs) = List.rev (to_list xs).
Proof.
  induction n;
  intros xs;
  dependent destruction xs.
  simpl. reflexivity.
  rewrite reverse_cons.
  rewrite to_list_shiftin.
  simpl.
  fold (to_list xs).
  rewrite IHn.
  reflexivity.
Qed.

(** [fold] *)

Lemma fold_right_lv :
  forall A B (P : A -> B -> B) n (xs : t A n) (b : B),
    fold_right P xs b = List.fold_right P b (to_list xs).
Proof.
  intros A B P .
  induction n ;
  intros xs b ;
  dependent destruction xs.
  simpl. auto.
  simpl.
  eapply f_equal.
  eauto.
Qed.
  
Lemma fold_right_app_vec : 
  forall (A B: Type) (P : A -> B -> B) n (l l' : t A n) i,
    fold_right P (append l l') i = fold_right P  l (fold_right P l' i).
Proof.
  intros A B P n l l' i.
  repeat rewrite fold_right_lv.
  rewrite to_list_append.
  rewrite List.fold_right_app.
  reflexivity.
Qed.

Lemma fold_right_shiftin:
  forall (A B: Type) (P : A -> B -> B) n (x : A) (xs : t A n) (b : B),
    fold_right P (shiftin x xs) b = fold_right P xs (P x b).  
Proof.
  intros A B P.
  induction n ;
    intros x xs b ;
    dependent destruction xs.
  simpl. auto.
  simpl. 
  rewrite IHn.
  reflexivity.
Qed.

(** [rmap] *)

(* We had defined this function directly as map f (reverse xs),
but then it produced a non strictly positive ocurrence in Compiler.v 
(see the compilation of operators) *)
Definition rmap {A} {B} (f : A -> B) : forall {n} (v:t A n), t B n :=
  fix rmap_fix {n} (v : t A n) : t B n := 
  match v with
    | [] => []
    | a :: v' => shiftin (f a) (rmap_fix v')
  end.

Lemma rmap_reverse:
  forall (A B : Type) (f : A -> B) n (v : t A n),
  rmap f v = map f (reverse v).
Proof.
  intros A B f.
  induction n ;
  intro xs ;
  dependent destruction xs.
  simpl. reflexivity.
  rewrite reverse_cons.
  simpl.
  rewrite shiftin_map.
  rewrite IHn.
  reflexivity.
Qed.

(** More helpers *)

Lemma Forall_weak:
  forall (A : Type) (P : A -> Prop) n (x : A) (xs : t A n),
    Forall P (x :: xs) -> Forall P xs.
Proof.
  intros A P n x xs Q.
  inversion Q.
  subst.
  apply inj_pair2_eq_dec in H1.
  subst. auto.
  eapply eq_nat_dec.
Qed.

Lemma Forall_Forall:
  forall (A : Type) (P : A -> Prop) n (xs : t A n),
    Forall P xs <-> List.Forall P (to_list xs).
Proof.
  intros A P.
  induction n ;
  intros xs ;
  dependent destruction xs ;
  simpl ;
  split ;
  intro Q ;
  constructor.
  inversion Q. subst. auto.
  eapply IHn.
  eapply Forall_weak. eauto.
  unfold to_list in Q.
  fold (to_list xs) in Q.
  inversion Q. subst. auto.
  inversion Q. subst.
  eapply IHn.
  auto.
Qed.
  
Lemma map_map_vec:
  forall (A B C : Type) (f : A -> B) (g : B -> C) 
         n (v : t A n),
    map g (map f v) = map (fun x => g (f x)) v.
Proof.
  intros A B C f g.
  induction n ;
  intros v ;
  dependent destruction v ;
  simpl ;
  auto.
  rewrite IHn.
  auto.
Qed.
