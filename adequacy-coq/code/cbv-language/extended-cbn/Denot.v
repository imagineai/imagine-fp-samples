(** * Denot : Denotational semantics *)
Set Automatic Coercions Import.
Require Import Source.
Require Import Common.
Require Import Arith.
Require Import Vector.
Require Import List.
Require Import Util.
Require Import Operator.
Require Import NaryFunctions.
Require Import PredomAll.
Require Import PredomMore.
Require Import PredomNary.
Require Import Coq.Program.Equality.
Require Import VecList.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Semantics of types and contexts *)

Fixpoint ty_denot (θ : type) : cppoType :=
  match θ with
      | ty_int => natFlat
      | θ1 ⇾ θ2 => ty_denot θ1 -=> ty_denot θ2
      | θ1 × θ2 => ty_denot θ1 * ty_denot θ2
  end.

Fixpoint ctx_denot (ctx : context) : cppoType :=
  match ctx with
      | nil => One
      | θ :: ctx =>  ctx_denot ctx * ty_denot θ
  end.

(** * Semantics of variables *)

Fixpoint var_denot ctx n a :
  lookup ctx n = Some a -> (ctx_denot ctx =-> ty_denot a).
refine (
    match ctx as ctx0 return 
          (lookup ctx0 n = Some a -> ctx_denot ctx0 =-> ty_denot a) with
      | nil => fun _ => _
      | (a0 :: ctx') => 
        match n as n0 return 
              (lookup (a0 :: ctx') n0 = Some a 
               -> ctx_denot (a0 :: ctx') =-> ty_denot a) 
        with
            0   => fun q => 
                     match q with
                         Logic.eq_refl => SND _ _
                     end
          | S n => fun _ => var_denot ctx' n _ _ << pi1
        end
    end
  ).
unfold lookup in *.
rewrite nth_error_nil in e.
discriminate.
simpl in e.
exact e.
Defined.

(* var_denot 0 (e, d) = d *)
Lemma var_denot_0:
  forall ctx a (L : lookup (a :: ctx) 0 = Some a),
    var_denot L = SND _ _.
Proof.
  intros.
  simpl.
  simpl in L.
  dependent destruction L.
  auto.
Qed.

(* var_denot (S n) (e, d) = var_denot n e *)
Lemma var_denot_S:
  forall ctx a n (L : lookup (a :: ctx) (S n) = Some a),
    forall e : ctx_denot ctx,
    forall d : ty_denot a,
    @var_denot _ (S n) _ L (e, d) = @var_denot _ n _ L e.
Proof.
  intros ctx a n L.
  intros e d.
  simpl.
  auto.
Qed.

(** * Sematics of conditionals *)

Definition cond (O : cpoType) : natDis -> (O * O -=> O) :=
  fun n =>
    match n with
        0 => pi1
      | _ => pi2
    end.

Definition condc (O : cpoType) := fcontD _ _ (cond O) .

(** * Semantics of terms *)


Fixpoint term_denot ctx θ (t : term ctx θ) :
  ctx_denot ctx =-> ty_denot θ :=
  match t in term _ θ1 return (ctx_denot ctx =-> ty_denot θ1) with
    | term_abs _ _ t  => exp_fun (term_denot t)
    | term_app _ _ t1 t2 
      => ev << <| term_denot t1 , term_denot t2 |>
    | term_var n a lu => var_denot lu
    | term_fix _ t => FIXP << term_denot t
    | term_const m  => @const _ _ (Val m)
    | term_op n opr qt  =>  
      nuncurry natFlat  _ _ (op_denot opr) 
               << to_natFlatn (Vector.map (@term_denot _ _) qt)
    | term_pair _ _ q0 q1 => 
      <| term_denot  q0, term_denot q1 |>
    | term_fst _ _ q => pi1 << (term_denot q)
    | term_snd _ _ q => pi2 << (term_denot q)
    | term_cond _ qi qp => 
      Categories.uncurry (GKL (condc _)) 
                         << <| term_denot qi, term_denot qp |>
  end.

Arguments term_denot [ctx θ] t.

(** * Properties about the semantics of operators *)

Definition term_denot_vec ctx a n
           (xs : t (term ctx a) n)
           (e : ctx_denot ctx) 
  := Vector.map (fun t => (term_denot t) e) xs.

Lemma op_terms_application:
  forall n (op : operator (S n)) ctx,
  forall (args : t (term ctx ty_int) (S n)),
  forall (e : ctx_denot ctx),
    sop_fapply (op_denot op) (term_denot_vec args e) 
       = term_denot (term_op op args) e.
Proof.
  intros n op ctx args e.
  rewrite sop_fapply_nuncurry.
  set (df := Vector.map (term_denot (θ:=ty_int)) args).
  replace (term_denot (term_op op args) e) with
  (PredomNary.nuncurry natFlat _ _ (op_denot op) (to_natFlatn df e))
    by auto.
  rewrite to_natFlat_vec.
  unfold df.
  rewrite map_map_vec.
  auto.
Qed.
 
Definition term_denot_list ctx a 
           (xs : list (term ctx a)) (e : ctx_denot ctx)
: list (ty_denot a) :=  map (fun t => (term_denot t) e) xs.
      
Lemma op_denot_fapply_terms: 
     forall n (op : operator (S n)) ctx
            (args : t (term ctx ty_int) (S n))
            (e : ctx_denot ctx),
       op_denot_fapply op (term_denot_list (to_list args) e) =
       Some ((term_denot (term_op op args)) e).
Proof.
  intros n op ctx args e.
  set (xs := term_denot_list (to_list args) e).
  set (ys := term_denot (term_op op args) e).
  assert (length xs = S n) as E0.
  unfold xs.
  unfold term_denot_list.
  rewrite map_length.
  apply to_list_length.
  set (X := op_denot_fapply_length2 op E0).
  destruct X as [v [Q0 Q1]].
  rewrite Q1.
  eapply f_equal.
  assert (v = term_denot_vec args e) as H.
  eapply to_list_inj.
  transitivity xs.
  eapply (of_list_option_def _ Q0).
  unfold xs.
  generalize args.
  generalize n.+1.
  clear.
  induction n.
  intros args.
  dependent destruction args.
  simpl. unfold to_list. auto.
  intros args.
  dependent destruction args.
  simpl.
  unfold to_list.
  fold (to_list args).
  rewrite IHn. auto.
  rewrite H.
  eapply op_terms_application.
Qed.

(** * Properties about the semantics of conditionals *)

Lemma GKL_condc_strict_num':
  forall (O : cppoType) (d : ty_denot ty_int),
    d =-= PBot ->
    GKL (condc O) d =-= PBot.
Proof.
  intros O d E.
  rewrite E.
  rewrite GKL_simpl.
  eapply gkl_strict.
Qed.

Lemma GKL_condc_strict_num:
  forall (d : ty_denot ty_int) (O : cppoType) (d0 d1: O),
    d =-= PBot ->
    GKL (condc _) d (d0, d1) =-= PBot.
Proof.
  intros d O d0 d1 Q.
  transitivity ((PBot : O * O -=> O) (d0, d1)).
  eapply fmon_eq_elim.
  eapply GKL_condc_strict_num'.
  auto.
  eapply PBot_app.
Qed.

Lemma condc_strict:
  forall (O : cppoType) (x : (O * O)%CAT) n,
    x =-= PBot ->
    condc _ n x =-= PBot.
Proof.
  intros O x n E.
  destruct n ;
  simpl ;
  split ; eapply E.
Qed.

Lemma GKL_condc_strict:
  forall (O : cppoType) (d : natFlat) (d' : (O * O)%CAT),
    d' =-= PBot ->
    (GKL (condc _) d) d' =-= PBot.
Proof.
  intros O d d' E.
  eapply GKL_respects_strictness.
  intros n d0 E0.
  eapply condc_strict.
  auto. auto.
Qed.