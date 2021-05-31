(** * DenApprox: The denotational approximation *)
Add LoadPath "./domain-theory".
Set Automatic Coercions Import.
Require Import Arith.
Require Import Util.
Require Import Common.
Require Import Basics.
Require Import Source.
Require Import Target.
Require Import Denot.
Require Import Biorthogonality.
Require Import StepIndexing.
Require Import List.
Require Import Sets.
Require Import Rel.
Require Import PredomCore.
Require Import PredomAll.
Require Import PredomMore.
Require Import RelDefs.
Require Import Sequences.
Require Import Operator.
Require Import SemChain.
Require Import Compiler.
Require Import VecList.
Require Import Denot.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Definition of the set of observations

A set of configurations closed by anti-execution and 
with an excluded closure. *)

Record RelT := mkrel {
   rel :> Rel closure stack;
   antiE :> antiexec rel;
   excluded :> exists g, forall s, ~ rel g s
}.

Section DenApprox.
  Variable R : RelT. 
  
  (** * Denotational approximation and its properties *)

  Definition dclos (a : type) (X : Power_set closure) 
  : closure -> ty_denot a -> Prop := 
    fun g d => In _ (bclos R X) g.

  (** Definition of the denotational approximation *)
  Fixpoint dapprox (a : type) : closure -> ty_denot a -> Prop :=
    match a as a0 return closure -> ty_denot a0 -> Prop with
      ty_int => fun g d => 
                  d =-= PBot 
                  \/ exists m h, g = [iconst m, h] /\ d =-= Val m
    | ty_arrow a b => 
      let dapproxc a (g : closure) d := @dclos a (fun g => dapprox g d) g d in 
      fun g f =>
        (forall d, f d =-= PBot) \/
        exists c h, 
          g = [igrab c, h] /\
          forall g' d, 
            dapproxc a g' d ->
            dapproxc b ([c, g' :: h]) (f d)
    | ty_prod a b =>
      let dapproxc a g d := @dclos a (fun g => dapprox g d) g d in 
      fun g d => 
        d =-= PBot \/
        exists c0 c1 h,
          let (d0, d1) := d in
          g = [ipair c0 c1, h] /\
          dapproxc a ([c0, h]) d0 /\
          dapproxc b ([c1, h]) d1
    end.
  
  Definition dapprox_set (a : type) (d : ty_denot a) : Power_set closure :=
    fun g => dapprox g d.
  
  Definition dapproxc (a : type) : Rel closure (ty_denot a) :=
    fun g d => dclos (dapprox_set d) g d.

  Lemma dapprox_dapproxc:
    forall a d g, @dapprox a d g -> @dapproxc a d g.
  Proof.
    intros a d k g Q.
    assert (cl := bclos_clos R).
    eapply (f_extensive cl).
    auto.
  Qed.

  (** Aproximation of a constant *)
  Lemma dapproxc_const:
    forall m (d : natFlat) h,
      d =-= Val m ->
      @dapproxc ty_int ([iconst m, h]) d.
  Proof.
    intros m d h Q.
    eapply dapprox_dapproxc.
    right.
    eexists. eexists.
    split. eauto. auto.
  Qed.

  (** [PBot] is always a denotational approximation *)
  Lemma dapprox_set_bot : forall a g, dapprox g (PBot : ty_denot a).
  Proof.
    intros a g.
    induction a ;
      simpl ; auto.
  Qed.

  Lemma dapproxc_bot : forall a g, dapproxc g (PBot : ty_denot a).
  Proof.
    intros.
    eapply dapprox_dapproxc.
    eapply dapprox_set_bot.
  Qed.
  
  Lemma dapprox_set_bot2:
    forall a, Same_set _ (@dapprox_set a PBot) (Full_set _).
  Proof.
    intros a.
    split.
    intros ? ?. 
    constructor.
    intros b Q.
    clear Q.
    unfold In.
    unfold dapprox_set.
    eapply dapprox_set_bot.
  Qed.
  
  Definition bbot_dapprox_set (a : type) (d : ty_denot a) : Power_set stack :=
    bbot R (dapprox_set d).
  
  Lemma bbot_dapprox_set_bot:
    forall a,
      Same_set _ (@bbot_dapprox_set a PBot) (Empty_set _).
  Proof.
    intros a.
    transitivity (bbot R (Full_set _)).
    unfold bbot_dapprox_set.
    eapply bbot_same_morphism.
    eapply dapprox_set_bot2.
    eapply bbot_full.
    (* third hyp of RelT used here: *)
    eapply R. 
  Qed.

  (** * Unfolding the orthogonal operators *)

  Lemma rel_from_dapproxc : 
    forall a d g s, @dapproxc a g d -> bbot_dapprox_set d s -> rel R g s.
  Proof.
    intros a d g s Hd Hs.
    eapply Hd. apply Hs.
  Qed.  

  Lemma rel_from_execution:
    forall a (d : ty_denot a) g g' s,
      bbot_dapprox_set d s ->
      dapproxc g d ->
      forall s',
      star trans (g', s') (g, s) ->
      rel R g' s'.
  Proof.
    intros a d g g' s T Q s' E.
    eapply antiexec_also_star.
    eapply R.
    exact E.
    eapply rel_from_dapproxc ;
    eauto.
  Qed.

  (* Convenient reorder of hypothesis *)
  Lemma rel_from_execution2:
    forall a (d : ty_denot a) g g' s s',
      dapproxc g d ->
      star trans (g', s') (g, s) ->
      bbot_dapprox_set d s ->
      rel R g' s'.
  Proof.
    intros.
    eapply rel_from_execution ;
    eauto.
  Qed.

  (** * Stability of the logical relation *)

Definition rel_stable (A : Type) (B : cpoType) (r : Rel A B) :=
    forall b0 b1, 
      b0 =-= b1 -> 
      forall a,  r a b0 -> r a b1.
           
  Lemma dapprox_dapproxc_stable:
    forall a,
    rel_stable (@dapprox a) ->
    rel_stable (@dapproxc a). 
  Proof.
    intro a.
    intro Q.
    unfold rel_stable.
    intros d d' E.
    intros g gad.
    unfold dapproxc.
    unfold dclos.
    assert (Same_set _ (dapprox_set d) (dapprox_set d')) as L0.
    split ;
    intros ? ?;
    eapply Q ;
    eauto.
    assert (Same_set _ (bclos R (dapprox_set d)) (bclos R (dapprox_set d'))) 
      as L1.
    eapply btop_same_morphism.
    eapply bbot_same_morphism.
    exact L0.
    eapply L1.
    assumption.
  Qed.

  Lemma dapprox_stable : 
    forall a, rel_stable (@dapprox a).
  Proof.
    induction a ;
    unfold rel_stable.
    intros d d' E g T.
    inversion T as [H | H].
    left.
    rewrite <- E.
    assumption.
    destruct H as [m [h [Q0 Q1]]].
    right.
    exists m. exists h. split ; auto.
    rewrite <- E. assumption.
    intros f f' Q g T.
    inversion T as [H | H].
    left. intro d.
    specialize (H d).
    rewrite <- H.
    eapply fmon_eq_elim.
    auto.
    destruct H as [c [h [Q0 Q1]]].
    right.
    exists c. exists h.
    split. auto.
    intros g' d A0.
    eapply dapprox_dapproxc_stable.
    auto.
    eapply fmon_eq_elim.
    exact Q.
    eapply Q1.
    auto.
    intros d d' Q g T.
    inversion T as [H | H].
    left. rewrite <- Q. auto.
    destruct d as (d0, d1).
    destruct d' as (d0', d1').
    destruct H as [c0 [c1 [h [Q0 [Q1 Q2]]]]].
    right.
    repeat eexists.
    eauto.
    eapply dapprox_dapproxc_stable.
    auto.
    eapply (prod_eq _ _ _ _ _ _ Q).
    assumption.
    eapply dapprox_dapproxc_stable.
    auto.
    eapply (prod_eq _ _ _ _ _ _ Q).
    auto.
  Qed.
  
  Lemma dapproxc_stable : 
    forall a, rel_stable (@dapproxc a).
  Proof.
    intro a.
    eapply dapprox_dapproxc_stable.
    eapply dapprox_stable.
  Qed.
    
  Lemma bbot_dapprox_set_stable:
    forall a  (d d' : ty_denot a), 
      d =-= d' -> 
      Same_set _ (bbot_dapprox_set d) (bbot_dapprox_set d').
  Proof.
    intros a d d' Q.
    eapply bbot_same_morphism.
    split ;
    intros ? ? ;
    eapply dapprox_stable.
    exact Q. auto. 
    symmetry. exact Q.
    auto.
  Qed.
    
  Lemma bbot_dapprox_set_bot2:
    forall a (d : ty_denot a),
    forall s,
      In _ (bbot_dapprox_set d) s ->
      ~ (d =-= PBot).
  Proof.
    intros a d s Q E.
    assert (In _ (bbot_dapprox_set (a:=a) PBot) s) as Q'.
    eapply bbot_dapprox_set_stable.
    symmetry. exact E. auto.
    assert (In _ (Empty_set _) s) as C.
    eapply bbot_dapprox_set_bot.
    exact Q'.
    destruct C.
  Qed.

     (** * A pointwise extension to environments *)
   Inductive dapproxctx : 
     list closure -> forall ctx, ctx_denot ctx -> Prop :=
   | dapproxctx_nil: @dapproxctx List.nil List.nil tt
   | dapproxctx_cons: 
       forall a g d h ctx e, 
         @dapproxc a g d ->
         @dapproxctx h ctx e ->
         @dapproxctx (g :: h) (a :: ctx)%list (e, d).

   Lemma dapproxctx_lookup:
     forall h ctx e,
       @dapproxctx h ctx e ->
       forall n a,
       forall H : lookup ctx n = Some a,
       exists g,
         lookup h n = Some g /\
         @dapproxc a g (var_denot H e).
   Proof.
     induction 1 as [ | a0 g d h ctx e H' Q Hip].
     intros n a H.
     contradict H.
     unfold lookup.
     rewrite nth_error_nil.
     intro. discriminate.
     destruct n.
     intros a H.
     simpl in H.
     injection H. intro. subst.
     exists g.
     split.
     reflexivity.
     rewrite var_denot_0.
     simpl.
     auto.
     intros a H.
     simpl in H.
     specialize (Hip n a H).
     destruct Hip as [g' [E0 E1]].
     exists g'.
     split.
     simpl.
     assumption.
     simpl.
     auto.
   Qed.

   (** Approximation and lookup *)
   Lemma dapproxc_var:
     forall h ctx e,
       @dapproxctx h ctx e ->
       forall n a,
       forall H : lookup ctx n = Some a,
         @dapproxc a ([iaccess n, h]) (var_denot H e).
   Proof.
     intros h ctx e Q.
     intros n a H.
     set (L := dapproxctx_lookup Q H).
     destruct L as [g [E0 Q1]].
     intros s Q0.
     eapply rel_from_execution.
     exact Q0.
     eauto.
     eapply star_one.
     econstructor.
     auto.
   Qed.

  (** * Obtaining tests of different types *)

  (** Tests for arrow types *)
  Lemma dapprox_set_fun : 
    forall a b (f : ty_denot (a ⇾ b)) c s d,
      dapproxc c d ->
      bbot_dapprox_set (f d) s ->
      bbot_dapprox_set f (-[ c ] :: s).
  Proof.
    intros a b f c s d HArg HApp.
    set (Q := bbot_dapprox_set_bot2 HApp).
    clearbody Q.
    intros g' H'.
    destruct H' as [HBot | HGrab].
    contradict Q.
    specialize (HBot d). auto.
    destruct HGrab as [c0 [h [Heq H2]]].
    rewrite Heq.
    apply (antiE) with ([c0 , c :: h]) s.
    apply rel_from_dapproxc with b (f d).
    apply H2.
    auto.
    auto.
    constructor.
  Qed.

  (** Tests for product types *)
  Lemma dapprox_set_fst:
    forall a b (d : ty_denot a) (d' : ty_denot b) s h, 
      bbot_dapprox_set d s ->
      @bbot_dapprox_set (a × b) (d , d') (-[ifst , h] :: s).
  Proof.
    intros a b d d' s h Q.
    set (NBot := bbot_dapprox_set_bot2 Q).
    clearbody NBot.
    intros g' I.
    inversion I as [HBot | HPair].
    contradict NBot.
    split ; eapply HBot.
    destruct HPair as [c0 [c1 [h' [Q0 [Q1 Q2]]]]].
    rewrite Q0.
    eapply rel_from_execution.
    exact Q.
    exact Q1.
    eapply star_step.
    econstructor.
    eapply star_one.
    econstructor.
  Qed.

  Lemma dapprox_set_snd:
    forall a b (d : ty_denot a) (d' : ty_denot b) s h, 
      bbot_dapprox_set d' s ->
      @bbot_dapprox_set (a × b) (d , d') (-[isnd , h] :: s).
  Proof.
    intros a b d d' s h Q.
    set (NBot := bbot_dapprox_set_bot2 Q).
    clearbody NBot.
    intros g' I.
    inversion I as [HBot | HPair].
    contradict NBot.
    split ; eapply HBot.
    destruct HPair as [c0 [c1 [h' [Q0 [Q1 Q2]]]]].
    rewrite Q0.
    eapply rel_from_execution.
    exact Q.
    exact Q2.
    eapply star_step.
    econstructor.
    eapply star_one.
    econstructor.
  Qed.

  (** Pointwise extension to lists *)
  Definition dapproxc_all 
             (a : type) (cl : list closure) 
             (dl : list (ty_denot a)) :=
    Forall2 (@dapproxc a) cl dl.

  Lemma dapproxc_all_length:
    forall a cl dl,
      @dapproxc_all a cl dl ->
      length cl = length dl.
  Proof.
    intros.
    eapply forall2_length.
    eauto.
  Qed.

  (** Using frames to construct new tests *)
  Lemma dapprox_set_op:
    forall n (op : operator (S n)),
    forall (cl : list closure),
    forall (dl : list natFlat),
    forall (eargs : list nat),
      @dapproxc_all ty_int cl dl -> 
      forall d s r,
        let fr := stack_val_frame (frame_op _ op eargs cl) in 
        op_fapply_both eargs (d :: dl) op = Some r ->
        In _ (@bbot_dapprox_set ty_int r) s ->
        In _ (@bbot_dapprox_set ty_int d) (fr :: s).
  Proof.
     intros n op.
     induction cl as [g | g];
     intros dl eargs Q d s r fr E0 I ;
     set (RNB := bbot_dapprox_set_bot2 I) ;
     clearbody RNB.
     (* case cl = nil *)
     assert (dl = nil) as E.
     set (L := dapproxc_all_length Q).
     destruct dl ; simpl in L.
     auto. discriminate.
     subst dl.
     intros g T.
     inversion T as [H | H].
     contradict RNB.
     eapply op_fapply_both_bot.
     eauto. eauto.
     destruct H as [m [h [Q0 Q1]]].
     rewrite Q0.
     assert (all_values (d :: nil) (m :: nil)%list) as av.
     econstructor. assumption. constructor.
     set (H := op_fapply_both_values av E0).
     destruct H as [r' [P0 P1]].
     eapply rel_from_execution.
     exact I.
     eapply (dapproxc_const _ P1).
     eapply star_one.
     set (P := op_fapply_list_def P0).
     clearbody P.
     destruct P as [v' [T0 T1]].
     rewrite <- T1.
     unfold op_fapply.
     econstructor.
     auto.
     (* case cl not nil *)
     intros g' T.
     inversion T as [H | H].
     contradict RNB.
     eapply op_fapply_both_bot.
     exact H. eauto.
     destruct H as [m [h [G0 G1]]].
     rewrite G0.
     set (L := dapproxc_all_length Q).
     destruct dl as [ | d' dl'].
     simpl in L. discriminate.
     inversion Q as [H0 | g0 d0 cl0 dl0 Q0 Q1].
     subst.
     set (P := op_fapply_both_step3 G1 E0).
     clearbody P.
     destruct P as [d1 [P0 P1]].
     eapply rel_from_execution.
     eapply IHcl with (r := d1).
     exact Q1.
     exact P0.
     eapply bbot_dapprox_set_stable.
     symmetry.  exact P1. exact I.
     exact Q0.
     eapply star_one.
     econstructor.
  Qed.

  (** * Combining approximations *)
  
  (** Approximation of a function application *)
  Lemma dapproxc_fun:
    forall a b (f : ty_denot (a ⇾ b)) (d : ty_denot a) c c' h ,
      dapproxc ([c, h]) f ->
      dapproxc ([c', h]) d ->
      dapproxc ([ipush c' c, h]) (f d).
  Proof.
    intros a b f d c c' h Qf Qd.
    intros s T.
    eapply rel_from_execution2.
    exact Qf.
    eapply star_one.
    econstructor.
    eapply dapprox_set_fun ;
    eauto.
  Qed.

  Lemma dapproxc_fix:
    forall a c h (d : ty_denot a) (f : ty_denot (a ⇾ a)),
      dapproxc ([c, h]) f ->
      dapproxc ([ifix c, h]) d ->
      dapproxc ([ifix c, h]) (f d).
   Proof.
     intros a c h d f Qf Q.
     intros s T.
     eapply rel_from_execution.
     eapply dapprox_set_fun.
     exact Q.
     exact T.
     exact Qf.
     eapply star_one.
     econstructor.
   Qed.

   (** Approximation of projections *)
  Lemma dapproxc_fst:
    forall c h a b d0 d1,
      @dapproxc (a × b) ([c, h]) (d0, d1) ->
      @dapproxc a ([ipush ifst c, h]) d0.
  Proof.
    intros c h a b d0 d1 Q.
    intros s T.
    eapply rel_from_execution2.
    exact Q.
    eapply star_one.
    econstructor.
    eapply dapprox_set_fst.
    eauto.
  Qed.

  Lemma dapproxc_snd:
    forall c h a b d0 d1,
      @dapproxc (a × b) ([c, h]) (d0, d1) ->
      @dapproxc b ([ipush isnd c, h]) d1.
  Proof.
    intros c h a b d0 d1 Q.
    intros s T.
    eapply rel_from_execution2.
    exact Q.
    eapply star_one.
    econstructor.
    eapply dapprox_set_snd.
    eauto.
  Qed.

  (** Approximation of a conditional projection *)
  Lemma dapproxc_cond:
    forall (d : ty_denot ty_int),
    forall a (d0 d1 : ty_denot a),
    forall c c' h,
      @dapproxc (a × a) ([c, h]) (d0, d1) ->
      dapproxc ([c', h]) d ->
      dapproxc ([ipush c' c, h]) (GKL (condc _) d (d0, d1)).
  Proof.
    intros d a d0 d1 c c' h Q0 Q1.
    intros s Q2.
    set (RNB := bbot_dapprox_set_bot2 Q2).
    clearbody RNB.
    refine (rel_from_execution2 Q0 _ _).
    apply star_one.
    econstructor.
    intros g' T.
    inversion T as [HBOT | HPAIR].
    clear T.
    contradict RNB.
    eapply GKL_condc_strict. auto.
    destruct HPAIR as [c0 [c1 [h' [P0 [P1 P2]]]]].
    refine (rel_from_execution2 Q1 _ _).
    rewrite P0.
    apply star_one.
    econstructor.
    intros g0 T0.
    inversion T0 as [HBOT | HCONST].
    contradict RNB.
    eapply GKL_condc_strict_num. auto.
    destruct HCONST as [m  [h0 [E0 E1]]].
    rewrite E0.
    destruct (eq_nat_dec m 0) as [E | E].
    refine (rel_from_execution2 P1 _ _).
    eapply star_one.
    rewrite E.
    econstructor.
    rewrite E in E1.
    eapply bbot_dapprox_set_stable.
    2:exact Q2.
    rewrite (GKL_value _ _ _ _ _ E1).
    simpl. auto.
    refine (rel_from_execution2 P2 _ _).
    eapply star_one.
    econstructor. auto.
    eapply bbot_dapprox_set_stable.
    2:exact Q2.
    rewrite (GKL_value _ _ _ _ _ E1).
    destruct m. contradict E. auto.
    simpl. auto.
  Qed.

  Lemma dapproxc_cond':
    forall (d : ty_denot ty_int),
    forall a (d' : ty_denot (a × a)),
    forall c c' h,
      @dapproxc (a × a) ([c, h]) d' ->
      dapproxc ([c', h]) d ->
      dapproxc ([ipush c' c, h]) (GKL (condc _) d d').
  Proof.
    intros d a d' c c' h Q0 Q1.
    destruct d' as (d0, d1).
    intros.
    eapply dapproxc_cond ;
    eauto.
  Qed.
    
  (** Approximation of fully applied operators *)
  Lemma dapproxc_op:
    forall n (op : operator (S n)),
    forall (cod : list code),
    forall (h : env),
    forall (dl : list natFlat),
    forall r,
      @dapproxc_all ty_int (insert_env cod h) dl ->
      op_denot_fapply op dl = Some r -> 
      @dapproxc ty_int ([fold_right ipush (iframe _ op) (rev cod) , h]) r.
   Proof.
     intros n op cod h dl r Q0 Q1.
     intros s Q2.
     set (L := op_denot_fapply_length Q1). 
     clearbody L.
     set (L1 := dapproxc_all_length Q0).
     clearbody L1. 
     assert (length cod = length dl) as L2.
     pattern (length dl).
     rewrite <- L1.
     symmetry.
     eapply map_length.
     destruct dl as [ | d0 dl'].
     simpl in L. discriminate.
     destruct cod as [ | c cod'].
     simpl in L. discriminate.
     simpl in Q0.
     inversion Q0 as [H0 | g0 d1 cl0 dl0 Q3 Q4].
     subst.
     set (xs := insert_env cod' h).
     set (fr := stack_val_frame (frame_op _ op List.nil xs)).
     eapply rel_from_execution2 with (s := fr :: s).
     exact Q3.
     eapply star_trans.
     eapply star_push_seq.
     simpl.
     rewrite <- (to_stack_skipn cod' h s) at 2. 
     unfold fr in *. clear fr.
     eapply star_one.
     assert (length cod' = n) as E1.
     simpl in L2.
     injection L2.
     intro E2. simpl in L.
     injection L. intro E3.
     rewrite E2. exact E3.
     rewrite E1.
     econstructor.
     rewrite <- E1.
     eapply to_stack_firstn.
     eapply dapprox_set_op.
     exact Q4.
     eauto. eauto.
   Qed.

   (** * Approximation of compiled code *)

   (** Every member of the semantic chain is a denotational approximation *)
   Lemma correctness_dapprox:
     forall ctx a,
     forall (qt : term ctx a),
     forall h e,
       dapproxctx h e ->
       forall i,
         dapproxc ([compile qt, h]) (tdenot_chain qt i e).
   Proof.
     set (P ctx a (qt : term ctx a) := 
            forall h e, 
              dapproxctx h e -> 
              forall i, dapproxc ([compile qt, h]) (tdenot_chain qt i e)).
     intros ctx a qt.
     fold (P ctx a qt).
     generalize ctx a qt.
     clear.
     eapply term_ind2 ;
       unfold P in *.
     (* abst *)
     intros ctx a b qt Hip.
     intros h e erel.
     intro i.
     destruct i as [ | i].
     simpl.
     eapply dapproxc_bot.
     eapply dapprox_dapproxc.
     right.
     eexists. eexists.
     split.
     simpl. eauto.
     intros g' d Q0.
     simpl.
     eapply Hip.
     constructor.
     auto. auto.
     (* app *)
     intros ctx a b qt1 qt2 Hip1 Hip2.
     intros h e erel.
     destruct i as [ | i].
     simpl.
     eapply dapproxc_bot.
     intros s In0.
     simpl in *.
     eapply dapproxc_fun ;
     eauto.
     (* var *)
     intros ctx n a H h e erel.
     destruct i as [ | i].
     simpl.
     eapply dapproxc_bot.
     intros s In0.
     simpl in *.
     eapply dapproxc_var ;
     eauto.
     (* fix *)
     intros ctx a qt Hip h e erel.
     induction i.
     simpl.
     eapply dapproxc_bot.
     simpl in *.
     eapply dapproxc_fix.
     eapply Hip.
     auto. auto.
     (* const *)
     intros ctx m h e erel i.
     destruct i as [_ | i].
     simpl. 
     eapply dapproxc_bot.
     simpl.
     eapply dapproxc_const.
     auto.
     (* operator *)
     intros ctx n op v F.
     intros h e erel i.
     destruct i as [_ | i].
     simpl.
     eapply dapproxc_bot.
     rewrite compile_op_fold.
     rewrite map_rev.
     apply dapproxc_op 
     with (dl := term_denot_chain_list i (Vector.to_list v) e).
     clear - F erel.
     generalize n v F.
     clear F v n.
     induction 1.
     simpl. econstructor.
     simpl. econstructor.
     eauto. auto.
     set (vl := Vector.to_list v).
     assert (length (term_denot_chain_list i vl e) = S n) as Q.
     unfold term_denot_chain_list.
     rewrite map_length.
     rewrite to_list_length.
     auto.
     set (L := op_denot_fapply_length2 op Q).
     clearbody L.
     destruct L as [v' [Q0 Q1]].  
     set (L := term_denot_chain_of_list v e i).
     clearbody L.
         (* rewrite Q0 in Q1 does not work :S *)
     assert (Some v' = Some (term_denot_chain_vec i v e)) as T.
     rewrite <- Q0.
     rewrite <- L.
     auto.
     injection T. intro. subst.
     rewrite op_terms_application_chain in Q1.
     auto.
     (* pair *)
     intros ctx a b t1 t2.
     intros Hip1 Hip2.
     intros h e erel i.
     destruct i as [_ | i].
     simpl.
     eapply dapproxc_bot.
     eapply dapprox_dapproxc.
     right.
     eexists. eexists. eexists.
     simpl.
     split.
     eauto.
     split.
     eapply Hip1. eauto.
     eapply Hip2. eauto.
     (* fst *)
     intros ctx a b t Hip.
     intros h e erel.
     destruct i as [_ | i].
     simpl.
     eapply dapproxc_bot.
     simpl.
     intros s In0.
     eapply dapproxc_fst.
     specialize (Hip h e erel i).
     set (d := (tdenot_chain t i) e).
     fold d in Hip.
     assert (d = (fst d, snd d)) as H.
     destruct d as (d0, d1). simpl. auto.
     rewrite H in Hip.
     eapply Hip.
     auto.
     (* snd *)
     intros ctx a b t Hip.
     intros h e erel.
     destruct i as [_ | i].
     simpl.
     eapply dapproxc_bot.
     simpl.
     intros s In0.
     eapply dapproxc_snd.
     specialize (Hip h e erel i).
     set (d := (tdenot_chain t i) e).
     fold d in Hip.
     assert (d = (fst d, snd d)) as H.
     destruct d as (d0, d1). simpl. auto.
     rewrite H in Hip.
     eapply Hip.
     auto.
     (* cond *)
     intros ctx a ti tp.
     intros Hip0 Hip1.
     intros h e erel.
     intro i.
     destruct i as [_ | i].
     simpl.
     eapply dapproxc_bot.
     unfold compile.
     fold (compile ti).
     fold (compile tp).
     simpl.
     eapply dapproxc_cond' ;
     eauto.
   Qed.
   
   (** Using the fact that a semantic chain in a flat
domain contains its supremum *)
   Lemma correctness_int:
     forall ctx,
     forall (qt : term ctx ty_int),
     forall h e m,
       dapproxctx h e ->
       term_denot qt e =-= Val m ->
       @dapproxc ty_int ([compile qt, h]) (Val m).
   Proof.
     intros ctx qt h e m erel E.
     set (Q := tdenot_chain_lub qt).
     clearbody Q.
     assert (lub (tdenot_chain qt) e =-= Val m) as Q0.
     rewrite <- E. rewrite Q. simpl. auto.
     simpl in Q0.
     set (Q1 := lubval Q0). clearbody Q1.
     destruct Q1 as [k [d' [T0 T1]]].
     simpl in T0. 
     assert (d' = m). apply T1. subst.
     set (L := correctness_dapprox (qt := qt) erel).
     specialize (L k).
     eapply dapproxc_stable.
     exact T0.
     auto.
   Qed.
     
End DenApprox.

(** * A concrete instance of the set of observations *)

Definition to_const m : Rel closure stack :=
  fun g s => 
    exists h,
      star trans (g, s) ([iconst m, h], nil).

Lemma to_const_antiE: forall m, antiexec (to_const m).
Proof.
  intros m g0 g1 s0 s1 Q0 Q1.
  inversion Q0 as [h H].
  exists h.
  eapply star_step.
  exact Q1. exact H.
Qed.

Lemma const_blocked:
  forall m h, blocked trans ([iconst m, h], nil).
Proof.
  intros m h.
  intro. intro.
  inversion H.
Qed.

Lemma access_blocked:
  forall n s, blocked trans ([iaccess n, nil], s).
Proof.
  intros n s.
  intro. intro.
  inversion H.
  subst.
  match goal with
      | H : lookup nil n = Some g |- _ =>
        rename H into L
  end.
  unfold lookup in L.
  rewrite nth_error_nil in L.
  discriminate.
Qed.
  
Lemma to_const_excluded:
  forall m,
  exists g, 
    forall s,
      ~ (to_const m) g s.
Proof.
  exists ([iaccess 0, nil]).
  intro s.
  intro Q.
  unfold to_const in Q.
  destruct Q as [h Q].
  set (g' := [iaccess 0, nil]). 
  assert ((g' , s) = ([iconst m, h], nil)) as F.
  apply blocked_unique with (R := trans) (a := (g', s)).
  eapply trans_deterministic.
  eapply star_refl.
  unfold g'.
  eapply access_blocked.
  exact Q.
  eapply const_blocked.
  discriminate F.
Qed.

Definition to_const_T (m : nat) : RelT.
  refine (@mkrel (to_const m) _ _).
  eapply to_const_antiE.
  eapply to_const_excluded.
Defined.

(** * Correctness for convergent terms *)

(** Convergence to a constant *)
Definition converges_to (w : conf) m : Prop :=
  exists η, star trans w ([iconst m, η], nil).

(** Compilation of closed terms of ground types *)
Theorem correctness_int_convergent:
  forall (t : term nil ty_int) m,
    term_denot t tt =-= Val m ->
    converges_to ([compile t, nil], nil) m.
Proof.
  intros qt m E.
  set (g := [compile qt, nil]).
  change (to_const m g nil).
  eapply (rel_from_dapproxc (R := to_const_T m) (a := ty_int)).
  eapply (correctness_int (qt := qt)).
  econstructor.
  exact E.
  intros g' In.
  inversion In as [HBot | HOk].
  assert False as F.
  eapply PBot_incon_eq.
  eapply HBot.
  contradiction.
  destruct HOk as [m0 [h0 [Q0 Q1]]].
  rewrite Q0.
  set (E' := vinj Q1). clearbody E'.
  assert (m = m0) as E0.
  eapply (proj1 E').
  rewrite E0.
  simpl.
  unfold to_const.
  exists h0.
  eapply star_refl.
Qed.

(** * Admissible extension of the approximation relation *)

Section AdmissibleExtension.

  Variable R : RelT. 
  
  Inductive aapprox (a : type) (g : closure) : ty_denot a -> Prop :=
  | aapprox_ext : forall d : ty_denot a, dapproxc R g d -> aapprox g d
  | aapprox_clos :  
      forall c : natO -=> ty_denot a,
        (forall i, aapprox g (c i)) ->
        forall d : ty_denot a, 
          d =-= lub c ->
          aapprox g d.

  Lemma dapprox_aapprox:
    forall a g d, dapproxc R (a := a) g d -> aapprox g d.
  Proof.
    intros a g d Q.
    constructor. auto.
  Qed.

  Lemma correctness_aapprox:
     forall ctx a,
     forall (qt : term ctx a),
     forall h e,
       dapproxctx R h e ->
       aapprox ([compile qt, h]) (term_denot qt e).
   Proof.
     intros ctx a qt h e E.
     apply aapprox_clos
     with (c := fcont_app (tdenot_chain qt) e).
     intro i.
     eapply aapprox_ext.
     simpl.
     eapply correctness_dapprox.
     auto.
     rewrite <- fcont_lub_simpl.
     generalize e.
     eapply fmon_eq_elim.
     eapply tdenot_chain_lub.
   Qed.

   Definition fpred (c : code) (e : env) a (d : ty_denot a) : Prop :=
     aapprox ([ifix c, e]) d.

   Lemma fpred_bot:
     forall c e a (f : ty_denot (a ⇾ a)),
       @fpred c e a PBot.
   Proof.
     intros c e a f.
     eapply dapprox_aapprox.
     eapply dapproxc_bot.
   Qed.

   Lemma fpred_closed:
     forall c e a (f : ty_denot (a ⇾ a)),
       dapproxc R ([c, e]) f ->
       forall d : ty_denot a,
         @fpred c e a d ->
         @fpred c e a (f d).
   Proof.
     intros c e a f Q.
     induction 1 as [d Q0 | c' E1 E2 d E4].
     unfold fpred.
     constructor.
     eapply dapproxc_fix ;
       auto.
     eapply aapprox_clos.
     Focus 2.
    rewrite E4.
    rewrite lub_comp_eq.
    reflexivity.
    intro i.
    specialize (E2 i).
    simpl. 
    auto.
   Qed.
   
   Lemma fpred_admissible:
     forall c e a (f : ty_denot (a ⇾ a)),
       dapproxc R ([c, e]) f ->
       admissible (@fpred c e a).
   Proof.
     intros c e a f Q.
     unfold admissible.
     intros dc E.
     eapply aapprox_clos.
     intro n.
     specialize (E n).
     unfold fpred in E.
     eexact E.
     auto.
   Qed.
   
   Lemma aapprox_fix:
     forall c e a (f : ty_denot (a ⇾ a)),
       dapproxc R ([c, e]) f ->
       aapprox ([ifix c, e]) (fixp f).
   Proof.
     intros c e a f Q.
     set (P d := @fpred c e a d).
     change (P (fixp f)). 
     eapply fixp_ind.
     eapply fpred_admissible.
     eauto.
     eapply fpred_bot. auto.
     eapply fpred_closed. auto.
   Qed.

End AdmissibleExtension.   
    
    

  
  
             