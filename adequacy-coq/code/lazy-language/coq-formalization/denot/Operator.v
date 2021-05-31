(** * Operator: Details of the semantics of operators *)
Add LoadPath "./domain-theory".
Set Automatic Coercions Import.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import Util.
Require Import Common.
Require Import NaryFunctions. 
Require Import PredomAll.
Require Import PredomNary.
Require Import List.
Require Import NaryFunctions.
Require Import PredomMore.
Require Import Coq.Program.Equality. 
Require Import Coq.Logic.Eqdep_dec.
Require Import Arith.
Require Import Vector.

Import VectorDef.VectorNotations.
Open Scope vector_scope.
Delimit Scope vector_scope with V.

(** A n-ary extension function *)
Fixpoint GKLv (P : cpoType) (D : cppoType) n 
: nmorph P n D =-> nmorph (PredomLift.liftCppoType P) n D :=
  match n return nmorph P n D =-> nmorph (PredomLift.liftCppoType P) n D with
      0 => Id
    | S n1 => GKLc << @pow_morph _ _ _ P (@GKLv P D n1)
  end.

(** A n-ary lifting function *)
Fixpoint etav (P0 P1 : cpoType) n
: nmorph P0 n P1 =-> nmorph P0 n (PredomLift.liftCppoType P1) :=
  match n return nmorph P0 n P1 =-> nmorph P0 n (liftCppoType P1) with
      0 => PredomLift.eta
    | S n => pow_morph _ (etav _ _ n)
  end.

(** Coercion of n-ary functions *)
Fixpoint nmorph_dis n : nfun nat n nat -> nmorph natDis n natDis :=
  match n return nfun nat n nat -> nmorph natDis n natDis with
      0 => id
    | S n0 => fun f => fcontD _ _ (fun x => nmorph_dis (f x))
  end.

Definition nmorph_lift n (f : nfun nat n nat) : nmorph natFlat n natFlat :=
  GKLv _ _ _ (etav _ _ _ (nmorph_dis f)).

(** An operator is a n-ary function over nat *)
Definition operator (n : nat) := nfun nat n nat.

(** Full application of operators *)
Definition op_fapply n (op : operator n) (v : t nat n) : nat
:= nfun_fapply _ v op.

Lemma op_fapply_nil:
  forall (op : operator 0) (dl : t nat 0),
    op_fapply op dl = op.
Proof.
  intros op dl.
  dependent destruction dl.
  unfold op_fapply.
  simpl. auto.
Qed.

Lemma op_fapply_cons:
  forall n (op : operator (S n)) (d : nat) (v : t nat n),
    op_fapply op (d :: v) = op_fapply (op d) v.
Proof.
  intros n op d v.
  unfold op_fapply.
  simpl.
  auto.
Qed.

(** A n-ary function over the flat domain of naturals *)
Definition soperator (n : nat) := nmorph natFlat n natFlat.

Definition sop_fapply {n} (sop : soperator n) (v : t natFlat n) : natFlat
  := nmorph_fapply _ v sop.

(** The semantics of an operator is the lifting of its associated function *)
Definition op_denot n (op : operator n) : soperator n
  := nmorph_lift op.

Lemma op_denot_nil (op : operator 0):
  op_denot op = Val op.
Proof.
  unfold op_denot.
  unfold nmorph_lift.
  simpl.
  unfold id.
  auto.
Qed.

(** Characterization of the semantics *)

Lemma op_denot_cons n (op : operator (S n)):
forall d,
  op_denot op d =-= GKL (fcontD _ _ (fun x => op_denot (op x))) d.
Proof.
  intros d.
  unfold op_denot.
  unfold nmorph_lift.
  simpl.
  generalize d. clear d.
  eapply fmon_eq_elim.
  eapply GKL_stable.
  split; intro x; simpl; auto.
Qed.

Lemma op_denot_bot n (op : operator (S n)):
  forall d,
    d =-= PBot ->
    op_denot op d =-= PBot.
Proof.
  intros d Q.
  rewrite op_denot_cons.
  rewrite Q.
  rewrite GKL_simpl.
  eapply gkl_strict.
Qed.

Lemma op_denot_cons_val n (op : operator (S n)):
  forall d x,
    d =-= Val x ->
    op_denot op d =-= op_denot (op x).
Proof.
  intros d x Q.
  rewrite op_denot_cons.
  rewrite GKL_value.
  simpl.
  reflexivity.
  exact Q.
Qed.

(** Properties of the application of an operator *)

Lemma sop_fapply_nil (op: operator 0):
  forall (dl : t natFlat 0),
    sop_fapply (op_denot op) dl = Val op.
Proof.
  intros dl.
  dependent destruction dl.
  unfold sop_fapply.
  simpl.
  rewrite op_denot_nil.
  auto.
Qed.

Lemma sop_fapply_cons:
  forall n,   
  forall (op : operator (S n)),
  forall (dl : t natFlat n),
  forall (d : natFlat),
    sop_fapply (op_denot op) (d :: dl) = sop_fapply (op_denot op d) dl.
Proof.
  intros n op dl d.
  trivial.
Qed.

Lemma sop_fapply_cons_bot:
  forall n,   
  forall (op : operator (S n)),
  forall (dl : t natFlat n),
  forall (d : natFlat),
    d =-= PBot ->
    sop_fapply (op_denot op) (d :: dl) =-= PBot.
Proof.
  intros n op dl d Q.
  rewrite sop_fapply_cons.
  unfold sop_fapply.
  rewrite op_denot_bot.
  clear op.
  2:exact Q.
  clear Q.
  generalize n dl.
  clear dl n d.
  induction n ;
  intro dp ;
  dependent destruction dp.
  simpl. auto.
  simpl. auto.
Qed.

Lemma sop_fapply_step:
  forall n 
         (dl : t natFlat n) 
         (op : operator (S n)) 
         (d : natFlat) 
         (x : nat),
    d =-= Val x ->
    sop_fapply (op_denot op) (d :: dl) =-=
    sop_fapply (op_denot (op x)) dl.
Proof.
  intros n dl op d x Q.
  rewrite sop_fapply_cons.
  unfold sop_fapply.
  (* the next rewrite works since nmorph_fapply is monotone *)
  rewrite op_denot_cons_val.
  reflexivity.
  exact Q.
Qed.

Lemma sop_fapply_values:
  forall n (op : operator n) (v : t nat n),
    sop_fapply (op_denot op) (map PredomLift.eta v) =-= Val (op_fapply op v).
Proof.
  induction n.
  intros n op. 
  simpl.
  rewrite sop_fapply_nil.
  rewrite op_fapply_nil.
  auto.
  intros op v.
  dependent destruction v.
  simpl.
  rewrite sop_fapply_step.
  eapply IHn.
  reflexivity.
Qed.

Lemma sop_fapply_forall_values:
  forall n (op : operator n) (v : t nat n) (dv : t natFlat n),
    Forall2 (fun d x => d =-= Val x) dv v ->
    sop_fapply (op_denot op) dv =-= Val (op_fapply op v).
Proof.
  induction n.
  intros op v dv F.
  rewrite op_fapply_nil.
  rewrite sop_fapply_nil.
  auto.
  intros op v dv F.
  dependent destruction dv.
  inversion F.
  subst.
  repeat simpl_existT.
  subst.
  rewrite sop_fapply_step.
  eapply IHn ;
  eauto.
  eauto.
Qed.

(** Applying a list of arguments instead of a vector *)

Definition op_fapply_list {n} (op : operator n) (v : list nat) : option nat :=
  match of_list_option v n with
      Some v => Some (op_fapply op v)
    | None => None
  end.

Definition op_denot_fapply {n} (op : operator n) (l : list natFlat) 
: option natFlat :=
  match of_list_option l n with
      Some v => Some (sop_fapply (op_denot op) v)
    | None => None
  end.

(** Properties of the application of a list *)

Lemma op_denot_fapply_length:
  forall n (op : operator n) l d,
    op_denot_fapply op l = Some d ->
    length l = n.
Proof.
  intros n op l d Q.
  unfold op_denot_fapply in Q.
  destruct (option_dec (of_list_option l n)) as [H | H].
  rewrite H in Q. discriminate.
  destruct H as [v H].
  rewrite H in Q.
  eapply of_list_option_def.
  eauto.
Qed.

Lemma op_denot_fapply_length2:
  forall n (op : operator n) (l : list natFlat),
    length l = n ->
    exists v,
      of_list_option l n = Some v /\
      op_denot_fapply op l = Some (sop_fapply (op_denot op) v).
Proof.
  intros n op l Q.
  set (X := of_list_option_length _ Q).
  destruct X as [v [X Y]].
  exists v.
  split.
  auto.
  unfold op_denot_fapply.
  rewrite X.
  auto.
Qed.

Lemma op_fapply_list_def:
  forall n (op : operator n) (l : list nat),
    forall m,
      op_fapply_list op l = Some m ->
      exists v', 
        of_list_option l n = Some v' /\
        op_fapply op v' = m.
Proof.
  intros n op l m Q.
  unfold op_fapply_list in Q.
  destruct (option_dec (of_list_option l n)) as [E | E].
  rewrite E in Q. discriminate.
  destruct E as [v Q0].
  rewrite Q0 in Q.
  eexists.
  split.
  exact Q0.
  injection Q.
  trivial.
Qed.

(** A list of arguments where all of them are values *)
Definition all_values (dl : list natFlat) (l : list nat) : Prop :=
  List.Forall2 (fun d v => d =-= Val v) dl l.

Lemma all_values_inv:
  forall d dl x l,
    all_values (d :: dl) (x :: l) ->
    all_values dl l /\ d =-= Val x.
Proof.
  intros d dl x l Q.
  inversion Q.
  subst.
  split ; auto.
Qed.

(** Applying two lists of arguments, the first list contains only values *)
Fixpoint op_fapply_both (values: list nat)
(args: list natFlat) n {struct values} : operator n -> option natFlat :=
match values with
    List.nil => fun op =>
                  match of_list_option args n with
                      Some v => Some (sop_fapply (op_denot op) v)
                    | None => None
                  end
  | (x :: values')%list =>
    match n return (operator n -> option natFlat) with
        0 => fun op => None
      | S n0 => fun op => op_fapply_both values' args (op x)
    end
end.

(** Properties of the application of two lists *)

Lemma op_fapply_both_bot:
  forall values args n (op : operator n) d r,
    d =-= PBot ->
    op_fapply_both values (d :: args) op = Some r ->
    r =-= PBot.
Proof.
  induction values ;
  intros args n op d r Q E.
  simpl in E.
  destruct (option_dec (of_list_option (d :: args) n)) as [H | H].
  rewrite H in E.
  discriminate.
  destruct H as [v H].
  rewrite H in E.
  injection E. intro E0.
  rewrite <- E0.
  destruct n.
  rewrite of_list_option_nil_none in H.
  discriminate.
  dependent destruction v.
  match goal with
      | |- sop_fapply _ (h :: v) =-= _ => rename h into d'
  end.
  assert (d = d') as E'.
  eapply of_list_option_cons.
  eauto.
  rewrite <- E'.
  eapply sop_fapply_cons_bot.
  auto.
  simpl in E.
  destruct n.
  discriminate.
  eauto.
Qed.

Lemma op_fapply_both_length:
  forall values args n (op : operator n) d,
    op_fapply_both values args op = Some d ->
    (length values + length args)%N = n.
Proof.
  induction values.
  intros args n op d Q.
  simpl.
  unfold op_fapply_both in Q.
  destruct (option_dec (of_list_option args n)) as [H | H].
  rewrite H in Q. discriminate.
  destruct H as [v H].
  rewrite add0n.
  eapply of_list_option_def.
  eauto.
  intros args n op d Q.
  destruct n.
  unfold op_fapply_both in Q. discriminate.
  simpl in Q.  
  nat_norm.
  eapply f_equal.
  eauto.
Qed.

Lemma op_fapply_both_first_nil:
  forall n args (op : operator n) v,
    of_list_option args n = Some v ->
    op_fapply_both List.nil args op = Some (sop_fapply (op_denot op) v).
Proof.
  intros n args op v Q.
  unfold op_fapply_both.
  rewrite Q. auto.
Qed.

Lemma op_fapply_both_second_nil:
  forall eargs n (op : operator n) d,
    op_fapply_both eargs List.nil op = Some d ->
    exists v,
      of_list_option eargs n = Some v /\
      d =-= Val (op_fapply op v).
Proof.
  induction eargs as [H | m eargs Hip].
  intros n op d Q.
  destruct n.
  simpl in Q.
  injection Q. intro L. rewrite <- L. clear L.
  exists (nil _).
  split.
  eapply of_list_option_nil2.
  simpl.
  rewrite sop_fapply_nil.
  rewrite op_fapply_nil.
  auto.
  simpl in Q. discriminate.
  intros n op d Q.
  destruct n.
  simpl in Q. discriminate.
  simpl in Q.
  specialize (Hip _ (op m) d Q).
  destruct Hip as [v [E0 E1]].
  exists (m :: v).
  split.
  eapply of_list_option_cons2. auto.
  rewrite op_fapply_cons.
  exact E1.
Qed.

Lemma op_fapply_both_step:
  forall n values d args (op : operator n) x d0 d1,
    d =-= Val x ->
    op_fapply_both values (d :: args) op = Some d0 ->
    op_fapply_both (values ++ x :: List.nil) args op = Some d1 ->
    d0 =-= d1.
Proof.
  induction n.
  intros values d args op x d0 d1 V Q0 Q1.
  destruct values as [ | y ys].
  (* n=0, values = nil *)
  unfold op_fapply_both in Q0.
  destruct (option_dec (of_list_option (d :: args) 0)) as [H | H].
  rewrite H in Q0. discriminate.
  destruct H as [v H]. 
  simpl in Q0. discriminate.
  (* n=0, values = y :: ys *)
  unfold op_fapply_both in Q0. discriminate.
  (* n+1 *)
  intros values d args op x d0 d1 V Q0 Q1.
  destruct values as [ | y ys].
  (* n+1, values = nil *)
  unfold op_fapply_both in Q0.
  destruct (option_dec (of_list_option (d :: args) (succn n))) as [H | H].
  rewrite H in Q0. discriminate.
  destruct H as [v H].
  rewrite H in Q0.
  simpl in Q1.
  dependent destruction v.
  set (X := of_list_option_cons _ _ H). clearbody X.
  destruct X as [X R].
  injection Q0. intro L. rewrite <- L. clear L.
  rewrite <- R.
  rewrite X in Q1.
  injection Q1. intro L. rewrite <- L. clear L.
  eapply sop_fapply_step ;
  eauto. 
  simpl in Q0.
  rewrite <- app_comm_cons in Q1.
  simpl in Q1.
  eapply IHn ; eauto.
Qed.

Lemma op_fapply_both_step2:
  forall n (op : operator n) values d args  x d0,
    d =-= Val x ->
    op_fapply_both values (d :: args) op = Some d0 ->
    exists d1,
    op_fapply_both (values ++ x :: List.nil) args op = Some d1.
Proof.
  induction n.
  intros op values d args x d0 E Q.
  destruct values as [ | z values'].
  simpl in Q.
  discriminate.
  unfold op_fapply_both in Q.
  discriminate.
  intros op values d args x d0 E Q.
  destruct values as [ | z values'].
  simpl in Q.
  destruct (option_dec (of_list_option (d :: args) (succn n))) as [H | H].
  rewrite H in Q. discriminate.
  destruct H as [v H].
  rewrite H in Q.
  dependent destruction v.  
  set (X := of_list_option_cons _ _ H).
  destruct X as [H' R]. destruct R.
  simpl.
  rewrite H'.
  eexists. auto.
  simpl in Q.
  simpl.
  eauto.
Qed.  
 
Lemma op_fapply_both_step3:
  forall n (op : operator n) values d args  x d0,
    d =-= Val x ->
    op_fapply_both values (d :: args) op = Some d0 ->
    exists d1,
    op_fapply_both (values ++ x :: List.nil) args op = Some d1
    /\ d0 =-= d1.
Proof.
  intros n op values d args x d0 E Q.
  set (X := op_fapply_both_step2 E Q).
  destruct X as [d1 X].
  exists d1.
  split. exact X.
  eapply op_fapply_both_step.
  eauto.
  eauto.
  eauto.
Qed.

Lemma op_fapply_both_values:
  forall 
    (dl : list natFlat) 
    (values : list nat)
    (eargs  : list nat)
    n (op : operator n),
    all_values dl values ->
    forall d: natFlat, 
      op_fapply_both eargs dl op = Some d ->
      exists x,
        op_fapply_list op (eargs ++ values) = Some x /\
        d =-= Val x.
Proof.
  induction dl as [ | d' dl' Hip].
  (* dl = nil *)
  intros values eargs n op Q d L.
  inversion Q. subst.
  set (X := op_fapply_both_second_nil L).
  clearbody X.
  destruct X as [v [E1 E2]].
  exists (op_fapply op v).
  split.
  rewrite app_nil_r.
  unfold op_fapply_list.
  rewrite E1.
  auto. auto.
  (* dl =  d' :: dl' *)
  intros values eargs n op A d Q.
  inversion A as [ | b0 z b1 values' L A' b4].
  subst.
  set (X := op_fapply_both_step3 L Q).
  destruct X as [d1 [Q0 E]].
  specialize (Hip _ _ _ _ A' _ Q0).
  destruct Hip as [x [B C]].
  exists x.
  split.
  rewrite <- app_assoc in B.
  simpl in B.
  auto.
  transitivity d1.
  auto. auto.
Qed.

(** N-ary uncurryfication *)

(* tonatFlat, nuncurry, vec_to_prod *)
Fixpoint to_natFlatn {D : cppoType} {n} 
         (v : Vector.t (D -=> natFlat) n) : D -=> natFlatn n :=
  match v in (Vector.t _ n0) return (D -=> natFlatn n0) with
    | Vector.nil  => terminal_morph _
    | Vector.cons g _ v' => <| g , to_natFlatn v' |>
  end.

Lemma sop_fapply_nuncurry:
  forall n (sop : nmorph natFlat n natFlat) (v : t natFlat n) ,
    sop_fapply sop v 
    = @PredomNary.nuncurry _ natFlat natFlat n sop (vec_to_nprod _ _ v).
Proof.
  induction n.
  intros sop v.
  dependent destruction v.
  simpl.
  unfold sop_fapply.
  simpl. unfold id. auto.
  intros sop v.
  dependent destruction v.
  unfold sop_fapply. simpl.
  eauto.
Qed.

Lemma to_natFlat_vec:
  forall 
    (D : cppoType) n
    (df : t (D -=> natFlat) n)
    (e : D),
    to_natFlatn df e = 
    vec_to_nprod _ _ (Vector.map (fun f : (D -=> natFlat) => f e) df).  
Proof.
  induction n.
  intros df e.
  dependent destruction df.
  simpl. auto.
  intros df e.
  dependent destruction df.
  simpl.
  eapply f_equal.
  eauto.
Qed.
