(** * Util: Some useful functions *)
Require Import Arith.
Require Import NaryFunctions.
Require Import Vector .
Require Import VecList.
Require Import List.
From mathcomp Require Import ssrnat ssrbool.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Program.Equality.
Set Implicit Arguments.

(** From Coq's [leq] to Ssreflect's [leq] *)
Lemma le_le : forall n m, (n <= m)%coq_nat -> n <= m.
  intros n m Q.
  exact (introT (@leP n m) Q).
Qed.


(** Lookup a value in a list *)
Definition lookup a (xs : list a) (n : nat) : option a  :=  nth_error xs n.

Hint Unfold lookup.

(** Inserts an element at the end of the list *)
Definition rev_cons a (xs : list a) (x : a) :=  xs ++ (x :: List.nil).

(** Replaces the value of a list in a given position *)
Fixpoint replace a (xs : list a) (n : nat) (x : a) :=
  match n with
      0 => 
      match xs with
          List.nil => nil
        | (y :: xs)%list => (x :: xs)%list
      end
    | S n =>
      match xs with
          nil => nil
        | (y :: xs)%list => (y :: replace xs n x)%list
      end
  end.
 
(** Making a replacement does not change the size of the list *)
Lemma replace_length :
  forall a (n : nat) (xs : list a) (x : a),
    length xs = length (replace xs n x). 
Proof.
  induction n ;
  intros xs x ;
  induction xs ;
  simpl ;
  auto.
Qed.

(** A list is either empty or contains a last element *)
Lemma exists_last' :
  forall A (xs : list A) , xs = nil \/ exists x ys, xs = ys ++ x :: nil. 
Proof.
  intros.
  induction xs.
  left. auto.
  match goal with
      [H : _ \/ _ |- _] =>
      elim H ; intros
  end.
  right.
  eexists.
  exists nil.
  simpl.
  subst.
  eauto.
  right.
  repeat match goal with
             [H : exists _, _ |- _] =>
             elim H ; clear H ; intros
         end.
  eexists.
  eexists.
  match goal with
      [H : ?x = ?y |- _] =>
      rewrite H
  end.
  rewrite app_comm_cons.
  eauto.
Qed.
  
Lemma nth_error_nil :
  forall n A, @nth_error A nil n = None.
Proof.
  intros n A.
  case n ; simpl ; auto.
Qed.

Ltac inject :=
  match goal with
      [H : ?x = ?y |- _] =>
      injection H ; intros
  end.

Ltac join :=
  match goal with
      [H0 : ?x = ?y,
            H1 : ?x = ?z |- _] =>
      rewrite H0 in H1
  end.

Lemma leq_addS : forall (x y : nat), x .+1 <= y .+1 -> x <= y.
Proof.
  intros x y Q. 
  rewrite <- (leq_add2r 1).
  replace ((x + 1)%N) with ((x .+1)%N).
  replace ((y + 1)%N) with ((y .+1)%N).
  auto.
  symmetry.
  eapply addn1.
  symmetry.
  eapply addn1.
Qed.

Import VectorDef.VectorNotations.
Open Scope vector_scope.
Delimit Scope vector_scope with V.


(* Converts a list to a vector of a given length if possible *)
Definition of_list_option {A} (l : list A) (n : nat) : option (t A n) :=
  match eq_nat_dec (length l) n with
      left p => match p with
                    eq_refl => Some (of_list l)
                end
    | right _ => None
  end.

Lemma of_list_option_def:
  forall A (l : list A) (n : nat) v,
    of_list_option l n = Some v ->
    length l = n /\ to_list v = l.
Proof.
  intros A l n v Q.
  unfold of_list_option in Q.
  destruct (eq_nat_dec (length l) n) as [E | E].
  destruct E.
  split. auto.
  injection Q.
  intros L.
  rewrite <- L.
  eapply to_list_of_list.
  discriminate.
Qed.

Lemma of_list_option_def2:
  forall A (l : list A),
    of_list_option l (length l) = Some (of_list l).
Proof.
  intros A l.
  unfold of_list_option.
  destruct (eq_nat_dec (length l) (length l)) as [E | E].
  dependent destruction E.
  auto.
  contradict E. auto.
Qed.

Lemma of_list_option_length:
  forall A (l : list A) n,
  forall q : length l = n,
  exists v,
    of_list_option l n = Some v
    /\ v = match q in (_ = n0) with Logic.eq_refl => of_list l end.
Proof.
  intros A l n Q.
  unfold of_list_option.
  destruct (eq_nat_dec (length l) n) as [E | E].
  destruct E.
  exists (of_list l).
  split. auto.
  dependent destruction Q.
  auto.
  contradiction.
Qed.

Lemma of_list_option_length2:
  forall A (l : list A) n v,
    of_list_option l n = Some v ->
    exists q : length l = n,
      v = match q in (_ = n0) with Logic.eq_refl => of_list l end.
Proof.
  intros A l n v Q.
  set (X := of_list_option_def _ Q).
  set (E := proj1 X).
  set (Y := of_list_option_length _ E).
  destruct Y as [v' [Q' X']].
  rewrite Q in Q'.
  injection Q'. intro H.
  destruct H.
  exists E.
  auto.
Qed.

Lemma of_list_option_cons:
  forall A x  (n : nat) (l : list A) y (v : t A n),
    of_list_option (x :: l) (S n) = Some ((y :: v)%V) ->
    of_list_option l n = Some v /\ x = y.
Proof.
  intros A x n l y v Q.
  unfold of_list_option in Q.
  destruct (eq_nat_dec (length (x :: l)) n.+1) as [E | E].
  dependent destruction E.
  simpl in Q.
  injection Q.
  intros.
  simpl_existT.
  subst.
  split.
  eapply of_list_option_def2.
  auto.
  discriminate.
Qed.

Lemma of_list_option_cons2:
  forall A x (n : nat) (l : list A) (v : t A n),
    of_list_option l n = Some v ->
    of_list_option (x :: l) (S n) = Some (x :: v).
Proof.
  intros A x n l v Q.
  unfold of_list_option.
  destruct (eq_nat_dec (length (x :: l)) (S n)) as [H | H].
  dependent destruction H.
  simpl.
  rewrite of_list_option_def2 in Q.
  injection Q. intro L. rewrite L.
  auto.
  contradict H.
  simpl.
  apply f_equal.
  eapply of_list_option_def.
  eauto.
Qed.

Lemma of_list_option_nil:
  forall A (l : list A) v,
    of_list_option l 0 = Some v ->
    l = List.nil.
Proof.
  intros A l v.
  intros Q.
  set (X := of_list_option_def _ Q).
  set (Y := proj1 X).
  clearbody Y.
  destruct l.
  auto.
  simpl in Y.
  discriminate.
Qed.

Lemma of_list_option_nil_none:
  forall A (x : A) (l : list A),
    of_list_option (x :: l) 0 = None.
Proof.
  intros A x l.
  unfold of_list_option.
  destruct (eq_nat_dec (length (x :: l)) 0) as [H | H].
  simpl in H. discriminate.
  auto.
Qed.

Lemma of_list_option_nil2:
  forall A,
    of_list_option (nil : list A) 0 = Some [].
Proof.
  intro A.
  unfold of_list_option.
  destruct (eq_nat_dec (length nil) 0) as [H | H].
  dependent destruction H.
  auto.
  simpl in H.
  contradict H.
  auto.
Qed.

(** Full apply of n-ary function *)
Fixpoint nfun_fapply (A B : Type) n (args : Vector.t A n) : 
  nfun A n B -> B :=
match args in (Vector.t _ n0) return nfun A n0 B -> B with
    Vector.nil => fun f => f
  | Vector.cons a _ args' => fun f => @nfun_fapply _ _ _ args' (f a)
end.
  
Lemma forall2_length:
  forall A B,
  forall (xs : list A),
  forall (ys : list B),
  forall (P : A -> B -> Prop),
    Forall2 P xs ys ->
    length xs = length ys.
Proof.
  induction 1 as [H | a b xs ys Pab F Hip].
  auto.
  simpl.
  rewrite Hip.
  reflexivity.
Qed.

Lemma option_dec: 
  forall A (el: option A),
    el = None \/ exists w: A, el = Some w.

Proof.
  intros.
  destruct el.
  right; exists a; trivial.
  left; trivial.
Qed.