(** * Target : The target language *)
Set Automatic Coercions Import.
Require Import Common.
Require Import Operator.
Require Import Util.
Require Import List.
Set Implicit Arguments.

(** * Components of the machine *)

Inductive code :=
  | igrab : code -> code
  | ipush : code -> code -> code
  | iaccess : var -> code
  | ifix : code -> code
  | iconst : nat -> code
  | iframe : forall n, operator n -> code
  | ipair : code -> code -> code
  | ifst : code
  | isnd : code.

(** Machine closures *)
Inductive closure :=
  | closure_code : code -> list closure -> closure.

Notation "[ c , e ]" := (closure_code c e)
(at level 30 , no associativity).

(** Machine Environments *)
Definition env := list closure.

(** Frames : data structures used to implement strict operators *)
Inductive frame :=
  | frame_op : forall n, operator n -> list nat -> list closure -> frame.

(** Stack values *)
Inductive stack_val :=
  | stack_val_closure : closure -> stack_val
  | stack_val_frame : frame -> stack_val
  | stack_val_pair : closure -> closure -> stack_val.

Notation "-[ c , e ]" := (stack_val_closure (closure_code c e))
(at level 20 , no associativity).

Notation "-[ g ]" := (stack_val_closure g)
(at level 20 , no associativity).

Notation "-< c1 , c2 >-" := (stack_val_pair c1 c2)
(at level 19, no associativity).


(** Stack *)
Definition stack := list stack_val.

(** Take the first n closures from the top of the stack *)
Fixpoint firstn_closures (n : nat) (s : stack)  : option (list closure) :=
  match n with
      0 => Some nil
    | S n => match s with
                 nil => None
               | stack_val_closure g :: s => 
                 match firstn_closures n s with
                     None => None
                   | Some cs => Some (g :: cs)
                 end
               | _ :: s => None
             end
  end.

(** Configurations *)
Definition conf := (closure * stack) %type.

(** * Transitions *)
Inductive trans : conf -> conf -> Prop :=
| trans_grab : 
    forall c e g (s : stack),
      trans ([igrab c,  e], -[g] :: s ) ([c , g :: e], s)
| trans_push :
    forall c c' e (s : stack),
      trans ([ipush c' c , e], s) ([c ,  e], -[c' , e] :: s)
| trans_access :
    forall e n g (s : stack),
      lookup e n = Some g ->
      trans ([iaccess n ,  e], s) (g , s)
| trans_fix:
    forall e c (s : stack),
      trans ([ifix c, e], s) ([c, e], -[ifix c, e] :: s)
| trans_pair:
    forall s g c0 c1 e,
      trans ([ipair c0 c1, e], -[g] :: s)
            (g, -< [c0, e], [c1, e] >- :: s)      
| trans_fst:
    forall s g0 g1 e,
      trans ([ifst, e], -<g0, g1>- :: s) (g0, s)
| trans_snd:
    forall s g0 g1 e,
      trans ([isnd, e], -<g0, g1>- :: s) (g1, s)      
| trans_frame:
    forall e n g (s : stack) cs,
    forall (op : operator (S n)),
      firstn_closures n s = Some cs ->
      let f0 := frame_op _ op nil cs in 
      trans ([iframe _ op, e], -[g] :: s) 
            (g, stack_val_frame f0 :: skipn n s)
| trans_const_partial :
    forall m n s vs g cs e,
    forall (op : operator n),
      let f0 := frame_op _ op vs (g :: cs) in
      let f1 := frame_op _ op (rev_cons vs m) cs in 
      trans ([iconst m , e], stack_val_frame f0 :: s) 
            (g , stack_val_frame f1 :: s)
| trans_const_full : 
    forall n s v vs e ,
    forall (op : operator n),
    forall args,
      of_list_option (vs ++ v :: nil) n = Some args ->
      let f0 := frame_op _ op vs nil in
      trans ([iconst v, e], stack_val_frame f0 :: s) 
            ([iconst (nfun_fapply _ args op) , e], s)
| trans_const_z:
    forall s g0 g1 e,
      trans ([iconst 0, e], -< g0 , g1 >- :: s) (g0, s)
| trans_const_nz:
    forall s  g0 g1 e m,
      m <> 0 ->
      trans ([iconst m, e], -< g0 , g1 >- :: s) (g1, s).

Require Import Sequences.
Require Import Coq.Logic.Eqdep_dec.

Definition insert_env (l : list code) (h : env) : list closure
  := map (fun c => [c, h]) l.

Fixpoint to_stack (l : list code) (h : env) (s : stack) : stack :=
  match l with
      nil => s
    | (c :: cs)%list => (-[c, h] :: to_stack cs h s)%list
  end.

Lemma to_stack_firstn :
  forall (cod : list code) h s,
    firstn_closures (length cod) (to_stack cod h s) 
    = Some (insert_env cod h).
Proof.
  induction cod ;
  intros h s.
  simpl.
  reflexivity.
  unfold length.
  fold (length cod).
  simpl.
  rewrite IHcod.
  reflexivity.
Qed. 

Lemma to_stack_skipn :
  forall (cod : list code) h s,
    skipn (length cod) (to_stack cod h s) = s.
Proof.
  induction cod ;
  intros h s ;
  simpl.
  reflexivity.
  auto.
Qed.

Lemma star_push_seq:
  forall (cod : list code) h (s : stack) ins,
    let c  := fold_right ipush ins (rev cod) in
    star trans ([c , h], s) ([ins, h], to_stack cod h s).
Proof.
  induction cod ;
  intros h s ins c ;
  simpl in *.
  eapply star_refl.
  unfold c. clear c.
  rewrite fold_right_app.
  simpl.
  eapply star_trans.
  eapply IHcod.
  eapply star_one.
  econstructor.
Qed.

(** Determinism *)
Lemma trans_deterministic:
  deterministic trans.
Proof.
  unfold deterministic.
  induction 1 ;
  intros b' T ;
  inversion T ;
  clear T ;
  intros ;
  try subst ;
  try reflexivity ;
  eauto ;
  repeat 
    match goal with
      | f : frame |- ?X => 
        match X with
          | context [f] =>
            unfold f
          | _ => clear f
        end
    end ;
  repeat 
    match goal with
      |  H : ?x = ?y, H' : ?x = ?z |- _ =>
         rewrite H in H' ; 
           injection H'  ;  
           clear H ; 
           intros
    end ;
  try subst ;
  try reflexivity ;
  try 
    match goal with
      | op0 : operator ?n, op1 : operator ?n |- ?X = ?Y =>
        match X with
          | context [op0] =>
            match Y with
              | context [op1] =>
                assert (op0 = op1) as E
              | _ => fail
            end              
          | _ => fail
        end
    end ;
  try
    match goal with
      | H : 0 <> 0 |- _ =>
        contradict H ; auto
    end.
  eapply inj_pair2_eq_dec.
  eapply eq_nat_dec.
  eauto.
  subst.
  reflexivity.
  eapply inj_pair2_eq_dec.
  eapply eq_nat_dec.
  eauto.
  subst.
  reflexivity.
  eapply inj_pair2_eq_dec.
  eapply eq_nat_dec.
  eauto.
  subst.
  reflexivity.
Qed.
      

