(** * SemChain : Semantic chain *)
Add LoadPath "./domain-theory".
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
Require Import Denot.
Set Implicit Arguments.
Unset Strict Implicit.

(** Definition *)
(* Semantic chain, defined in two parts to prevent automatic unfolding *)
Definition term_denot_chain_body
           ctx a (qt : term ctx a) n 
           (F : forall {ctx} {a} (qt : term ctx a) (n : nat),  
                  ctx_denot ctx =-> ty_denot a) :=
  match qt in term _ a0 return (ctx_denot ctx =-> ty_denot a0) with
    | term_abs _ _ qt  => 
      exp_fun (F qt n)
    | term_app _ _ q1 q2 => 
      ev << <| F q1 n, F q2 n |>
    | term_var _ a lu => var_denot lu
    | term_fix a qt => 
      ev << <| F qt n, F (term_fix qt) n |>
    | term_const m  => @const _ _ (Val m)
    | term_op _ opr qt  =>
      nuncurry natFlat  _ _ (op_denot opr) << 
               to_natFlatn 
               (Vector.map (fun q => F q n) qt)
    | term_pair _ _ q0 q1 => <| F q0 n , F q1 n |>
    | term_fst _ _ q => pi1 << (F q n)
    | term_snd _ _ q => pi2 << (F q n)
    | term_cond _ qi qp =>
      Categories.uncurry (GKL (condc _)) << <| F qi n, F qp n |>
  end.

Fixpoint term_denot_chain ctx a (qt : term ctx a) (n : nat) {struct n} :
  ctx_denot ctx =-> ty_denot a :=
  match n with
      0 => @const _ _ (PBot : ty_denot a)
    | S n => term_denot_chain_body qt n term_denot_chain
  end.

(** Semantic chain of operators *)

Definition term_denot_chain_vec ctx a n
           (i : nat)
           (xs : t (term ctx a) n)
           (e : ctx_denot ctx) 
  := Vector.map (fun t => term_denot_chain t i e) xs.

Definition term_denot_chain_list ctx a (i : nat) 
           (xs : list (term ctx a)) (e : ctx_denot ctx)
: list (ty_denot a) :=  map (fun t => (term_denot_chain t i) e) xs.

Lemma op_terms_application_chain:
  forall n (op : operator (S n)) ctx,
  forall (args : t (term ctx ty_int) (S n)),
  forall i (e : ctx_denot ctx),
    sop_fapply (op_denot op) (term_denot_chain_vec i args e) 
       = term_denot_chain (term_op op args) (S i) e.
Proof.
  intros n op ctx args i e.
  rewrite sop_fapply_nuncurry.
  set (df := Vector.map (fun q => term_denot_chain q i) args).
  replace (term_denot_chain (term_op op args) (S i) e) with
  (PredomNary.nuncurry natFlat _ _ (op_denot op) (to_natFlatn df e))
    by auto.
  rewrite to_natFlat_vec.
  unfold df.
  rewrite map_map_vec.
  auto.
Qed.

Lemma term_denot_chain_of_list:
  forall n ctx (v : t (term ctx ty_int) n) e i,
    of_list_option (term_denot_chain_list i (to_list v) e) n =
    Some (term_denot_chain_vec i v e).
Proof.
  induction n ;
  intros ctx v e i ;
  dependent destruction v ;
  simpl.
  rewrite of_list_option_nil2.
  auto.
  eapply of_list_option_cons2.
  eapply IHn.
Qed.

(** Semantic chain monotony *)

Lemma term_denot_chain_suc_forall:
  forall n ctx (v : t (term ctx ty_int) n) (e : ctx_denot ctx),
    Vector.Forall 
      (fun qt => 
         forall i, 
           term_denot_chain qt i <= term_denot_chain qt (S i)) v -> 
    forall i,
      vector_leq (term_denot_chain_vec i v e) (term_denot_chain_vec (S i) v e).
Proof.
  induction n ;
  intros ctx v e Q i ;
  dependent destruction v.
  simpl. econstructor.
  unfold term_denot_chain_vec.
  simpl.
  inversion Q as [ | L0 L1 L2 H0 H1 L3 L4].
  simpl_existT.
  subst.
  econstructor.
  eapply H0.
  specialize (IHn ctx v e H1 i).
  eauto.
Qed.

Lemma term_denot_chain_suc:
  forall ctx a (qt : term ctx a) i,
    term_denot_chain qt i <= term_denot_chain qt (S i).
Proof.
  set (P ctx a (qt : term ctx a) := 
         forall i, term_denot_chain qt i <= term_denot_chain qt (S i)).
  intros ctx a qt.
  fold (P ctx a qt).
  generalize ctx a qt.
  clear ctx a qt.
  eapply term_ind2 ;
  unfold P in * ;
  induction i ;
  try (intro env ; apply leastP) ;
  clear P ;
  intro eta ;
  simpl.
  (* abst *)
  intros d.
  simpl.
  eapply H.
  (* app *)
  eapply Ole_trans.
  eapply fmonotonic.
  eapply H0.
  eapply H.
  (* var *)
  trivial.
  (* fix *)
  eapply Ole_trans.
  eapply fmonotonic.
  eapply IHi.
  eapply H.
  (* const *)
  trivial.
  (* op *)
  set (F := fun (a b : ty_denot ty_int) => a <= b).
  change 
    (F (term_denot_chain (term_op op v) (S i) eta)
       (term_denot_chain (term_op op v) (S (S i)) eta)).
  rewrite <- op_terms_application_chain.
  rewrite <- op_terms_application_chain.
  unfold sop_fapply.
  unfold F.
  eapply nmorph_monotonic.
  eapply term_denot_chain_suc_forall.
  auto.
  (* pair *)
  split ; simpl.
  eapply H.
  eapply H0.
  (* fst *)
  eapply H.
  (* snd *)
  eapply H.
  (* cond *)
  fold (ty_denot a).
  set (F := GKL (condc (ty_denot a))).
  eapply Ole_trans.
  eapply fmonotonic.
  eapply H0.
  eapply fmon_leq_elim.
  eapply fmonotonic.
  eapply H.
Qed.

Lemma term_denot_chain_monotonic:
  forall ctx a (qt : term ctx a),
    monotonic (term_denot_chain qt).
Proof.
  intros ctx a qt.
  eapply chain_suc.
  eapply term_denot_chain_suc.
Qed.

Definition tdenot_chain ctx a (qt : term ctx a) := 
  @mk_fmono _ _ (term_denot_chain qt) (term_denot_chain_monotonic qt).

Definition term_denot_chain_seq {n} {ctx} 
           (v : t (term ctx ty_int) n) (e : ctx_denot ctx) :=
  Vector.map (fun qt => fcont_app (tdenot_chain qt) e) v.

(** Semantic chain least upper bound *)

Lemma term_denot_chain_seq_lub:
  forall n ctx (v : t (term ctx ty_int) n) (e : ctx_denot ctx),
    (Vector.Forall 
       (fun qt => term_denot qt =-= lub (tdenot_chain qt)) v) ->          
    vector_eq
      (term_denot_vec v e)
      (lub_vec (term_denot_chain_seq v e)).
Proof.
  induction 1.
  simpl.
  econstructor.
  simpl.
  econstructor.
  rewrite H.
  simpl.
  auto.
  auto.
Qed.

Lemma term_denot_chain_seq_proj:
  forall n ctx (v : t (term ctx ty_int) n) (e : ctx_denot ctx) j,
    vector_eq 
      (term_denot_chain_vec j v e)
      (Vector.map 
         (fun c : ordCatType natO natFlat => c j)
         (term_denot_chain_seq v e)).
Proof.
  induction n ;
  intros ctx v e j ;
  dependent destruction v.
  simpl.
  econstructor.
  econstructor.
  simpl. auto.
  change (
      vector_eq 
        (term_denot_chain_vec j v e)
        (Vector.map 
           (fun c : ordCatType natO natFlat => c j)
           (term_denot_chain_seq v e))).
  eauto.
Qed.

Lemma exp_fun_curry:
  forall (A B C : cpoType) (f : A * B =-> C),
    exp_fun f =-= @curry _ A B C f .
Proof.
  intros.
  eapply fmon_eq_intro.
  intro x.
  eapply fmon_eq_intro.
  intro y.
  simpl.
  auto.
Qed.

Lemma lub_stable:
  forall (A : cpoType),
  forall (c0 c1 : natO =-> A),
    c0 =-= c1 ->
    lub c0 =-= lub c1.
Proof.
  intros A c0 c1 Q.
  split ;
  eapply lub_mon ;
  eapply Q.
Qed.

Lemma prod_lub_simpl:
  forall (A B : cpoType),
  forall (c1 : natO =-> A),
  forall (c2 : natO =-> B),
    lub (<| c1, c2 |>) =-= (lub c1, lub c2).
Proof.
  intros.
  unfold lub at 1.
  simpl.
  unfold prod_lub.
  rewrite prod_fun_fst.
  rewrite prod_fun_snd.
  auto.
Qed.

Fixpoint app_chain (D : cppoType) (F : natO =-> (D -=> D)) (n : natO) :=
  match n with
      0 => PBot
    | S n => (F n) (app_chain F n)
  end.
  
Lemma app_chain_suc (D : cppoType) (F : natO =-> (D -=> D)):
  forall n, app_chain F n <= app_chain F (S n).
Proof.
  induction n.
  simpl.
  eapply leastP.
  simpl.
  transitivity ((F n) (app_chain F (S n))).
  eapply fmonotonic.
  eauto.
  eapply fmon_leq_elim.
  eapply fmonotonic.
  eapply leqnSn.
Qed.

Lemma app_chain_mono (D : cppoType) (F : natO =-> (D -=> D)):
  monotonic (app_chain F).
Proof.
  eapply chain_suc.
  eapply app_chain_suc.
Qed.
  
Definition appchain (D : cppoType) (F : natO =-> (D -=> D)) :=
  mk_fmono (app_chain_mono F).

Lemma app_chain_fixpoint_lt:
  forall (D : cppoType) (f : D -=> D) (F : natO =-> (D -=> D)),
    f =-= lub F ->
    lub (appchain F) <= FIXP f.
Proof.
  intros D f F Q.
  rewrite FIXP_simpl.
  unfold fixp.
  eapply lub_mon.
  change (forall n, appchain F n <= iter f n).
  induction n.
  simpl.
  eapply leastP.
  simpl.
  transitivity (f (app_chain F n)).
  eapply fmon_leq_elim.
  rewrite Q.
  eapply le_lub.
  eapply fmonotonic.
  auto.
Qed.

Lemma app_chain_fixpoint_gt:
  forall (D : cppoType) (f : D -=> D) (F : natO =-> (D -=> D)),
    f =-= lub F ->
    FIXP f <= lub (appchain F).
Proof.
  intros D f F Q.
  rewrite FIXP_simpl.
  set (P d := d <= lub (appchain F)).
  fold (P (fixp f)).
  eapply fixp_ind.
  (* admissible *)
  intros c. intro L.
  unfold P in *.
  eapply lub_le. auto.
  (* P PBot *)
  unfold P.  eapply leastP.
  (* forall x : D, P x -> P (f x) *)
  intros x Px.
  unfold P in *.
  rewrite Q.
  set (d := lub (appchain F)).
  fold d in Px.
  transitivity ((lub F) d).
  set (G := lub F).
  apply (@fmonotonic _ _ G).
  auto.
  simpl.
  eapply lub_le.
  intro n.
  simpl.
  (* (F n) d <= d *)
  unfold d.
  rewrite lub_comp_eq.
  eapply lub_le_compat_weak.
  intro i.
  destruct (le_dec i n) as [H0 | H0].
  exists (S n).
  simpl.
  eapply fmonotonic.
  eapply app_chain_mono.
  exact (le_le H0).
  set (H1 := not_le _ _ H0).
  clearbody H1.
  exists (S i).
  simpl.
  eapply fmon_leq_elim.
  eapply fmonotonic.
  transitivity (S n).
  eapply leqnSn.
  change (n < i).
  exact (le_le H1).
Qed.

Lemma app_chain_fixpoint:
  forall (D : cppoType) (f : D -=> D) (F : natO =-> (D -=> D)),
    f =-= lub F ->
    FIXP f =-= lub (appchain F).
Proof.
  intros D f F Q.
  split.
  eapply app_chain_fixpoint_gt.
  auto.
  eapply app_chain_fixpoint_lt.
  auto.
Qed.

Lemma tdenot_chain_lub:
  forall ctx a (qt : term ctx a),
    term_denot qt =-= lub (tdenot_chain qt).
Proof.
  intros ctx a qt.
  set (P ctx a (qt : term ctx a) 
       := term_denot qt =-= lub (tdenot_chain qt)). 
  fold (P ctx a qt).
  generalize ctx a qt.
  clear ctx a qt.
  eapply term_ind2 ;
  unfold P in * ;
  clear P.
  (* abst *)
  intros ctx a b qt Hip.
  unfold term_denot at 1.
  fold (term_denot qt).
  fold (ctx_denot ctx).
  eapply Oeq_trans.
  eapply exp_fun_curry.
  rewrite Hip.
  rewrite lub_comp_eq.
  symmetry.
  eapply Oeq_trans.
  eapply lub_lift_left with (n := 1).
  eapply lub_stable.
  eapply fmon_eq_intro.
  intro n.
  eapply fmon_eq_intro.
  intro eta.
  eapply fmon_eq_intro.
  intro d.
  simpl.
  auto.
  (* app *)
  intros ctx a b qt1 qt2 Hip1 Hip2.
  simpl.
  rewrite Hip1.
  rewrite Hip2.
  eapply fmon_eq_intro.
  intro eta.
  set (c1 := fcont_app (tdenot_chain qt1) eta).
  set (c2 := fcont_app (tdenot_chain qt2) eta).
  match goal with
      |- _ =-= ?Y =>
      set (Z := Y)
  end.
  change (ev (C := cpoExpType) (lub c1, lub c2) =-= Z).
  rewrite <- prod_lub_simpl.
  rewrite lub_comp_eq.
  fold (ty_denot b).
  symmetry.
  unfold Z.
  eapply Oeq_trans.
  eapply lub_lift_left with (n := 1).
  simpl.
  eapply lub_stable.
  eapply fmon_eq_intro.
  intro n.
  simpl. auto.
  (* var *)
  intros ctx n a H.
  symmetry.
  eapply Oeq_trans.
  eapply lub_lift_left with (n := 1).
  eapply lub_cte_chain.
  intro i.
  simpl.
  auto.
  (* fix *)
  intros ctx a t Hip.
  simpl.
  eapply fmon_eq_intro.
  intro eta.
  simpl.
  fold (ty_denot a).
  eapply Oeq_trans.
  apply app_chain_fixpoint.
  rewrite Hip.
  simpl.
  eauto.
  eapply lub_stable.
  eapply fmon_eq_intro.
  induction n.
  simpl. auto.
  simpl in *.
  rewrite IHn.
  auto.
  (* const *)
  intros ctx m.
  symmetry.
  eapply Oeq_trans.
  eapply lub_lift_left with (n := 1).
  eapply lub_cte_chain.
  intro i.
  simpl.
  auto.
  (* op *)
  intros ctx n op v HipFA.
  eapply fmon_eq_intro.
  intro eta.
  set (F := fun (a b : ty_denot ty_int) => a =-= b).
  change (F (term_denot (term_op op v) eta) 
            (lub (tdenot_chain (term_op op v)) eta)).
  rewrite <- op_terms_application.
  unfold F.
  eapply Oeq_trans.
  eapply nmorph_stable.
  eapply term_denot_chain_seq_lub.
  auto.
  rewrite nmorph_continuous.
  simpl.
  symmetry.
  eapply Oeq_trans.
  eapply lub_lift_left with (n := 1).
  eapply lub_stable.
  eapply fmon_eq_intro.
  intro j.
  match goal with
      |- ?X =-= ?Z => set (Y := Z)
  end.
  change (term_denot_chain (term_op op v) (S j) eta
                           =-= Y).
  rewrite <- op_terms_application_chain.
  unfold Y.
  simpl.
  unfold sop_fapply.
  unfold nmorph_fapply_seq.
  eapply nmorph_stable.
  eapply term_denot_chain_seq_proj.
  (* pair *)
  intros ctx a b qt1 qt2 Hip1 Hip2.
  simpl.
  eapply fmon_eq_intro.
  intro eta.
  simpl.
  rewrite Hip1.
  rewrite Hip2.
  simpl.
  rewrite <- prod_lub_simpl.
  symmetry.
  eapply Oeq_trans.
  eapply lub_lift_left with (n := 1).
  eapply lub_stable.
  eapply fmon_eq_intro.
  intro n.
  simpl. auto.
  (* fst *)
  intros ctx a b qt Hip.
  simpl.
  rewrite Hip.
  eapply fmon_eq_intro.
  intro eta.
  match goal with
      |- _ =-= ?Y =>
      set (Z := Y)
  end.
  change (pi1 (C := cpoExpType) (lub (tdenot_chain qt) eta) =-= Z).
  rewrite lub_comp_eq.
  simpl.
  symmetry.
  unfold Z.
  eapply Oeq_trans.
  eapply lub_lift_left with (n := 1).
  eapply lub_stable.
  eapply fmon_eq_intro.
  intro n.
  simpl.
  auto.
  (* snd *)
  intros ctx a b qt Hip.
  simpl.
  rewrite Hip.
  eapply fmon_eq_intro.
  intro eta.
  match goal with
      |- _ =-= ?Y =>
      set (Z := Y)
  end.
  change (pi2 (C := cpoExpType) (lub (tdenot_chain qt) eta) =-= Z).
  rewrite lub_comp_eq.
  simpl.
  symmetry.
  unfold Z.
  eapply Oeq_trans.
  eapply lub_lift_left with (n := 1).
  eapply lub_stable.
  eapply fmon_eq_intro.
  intro n.
  simpl.
  auto.
  (* cond *)
  intros ctx a ti tp Hip1 Hip2.
  simpl.
  fold (ty_denot a).
  eapply fmon_eq_intro.
  intro eta.
  match goal with
      |- _ =-= ?Y =>
      set (Z := Y)
  end.
  set (F := Categories.uncurry (GKL (condc _))).
  change (F (<| term_denot ti, term_denot tp |> eta)  =-= Z).
  rewrite Hip1.
  rewrite Hip2.
  set (c1 := fcont_app (tdenot_chain ti) eta).
  set (c2 := fcont_app (tdenot_chain tp) eta).
  change (F (lub c1, lub c2) =-= Z).
  rewrite <- prod_lub_simpl.
  rewrite lub_comp_eq.
  symmetry.
  eapply Oeq_trans.
  unfold Z.
  eapply lub_lift_left with (n := 1).
  eapply lub_stable.
  eapply fmon_eq_intro.
  intro n.
  simpl.
  auto.
Qed.

