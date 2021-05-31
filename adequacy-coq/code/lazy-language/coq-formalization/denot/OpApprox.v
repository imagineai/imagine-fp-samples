(** * OpApprox : The operational approximation *)
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
Require Import Vector.
Require Import List.
Require Import Sets.
Require Import Rel.
Require Import Sequences.
Require Import VecList.
Require Import NaryFunctions.
Require Import PredomAll.
Require Import PredomMore.
Require Import Operator.
Require Import Compiler.
Require Import Coq.Program.Equality.
Require Import RelDefs.
Set Implicit Arguments.
  
(** * Definition of the set of observations *)

Record RelE : Type := 
  mkrel {
      rel :> iRel closure stack;
      stepI :> StepI (irel_reli rel);
      antiE :> iantiexec rel
    }.

Lemma antiexec_weak:
  forall (R : RelE) i,
    antiexec (rel R i).
Proof.
    intros R i.
    intros g0 g1 s0 s1 Ri T.
    rewrite rel_equiv.
    eapply (decreasing (stepI R)).
    rewrite <- rel_equiv.
    eapply antiE.
    eauto.
    auto.
Qed.

Lemma antiexec_star_weak:
  forall (R : RelE) i,
    antiexec_star (rel R i).
Proof.
  intros R i.
  eapply antiexec_also_star.
  eapply antiexec_weak.
Qed.

Section OpApprox.
  Variable R : RelE.

  (** * Operational approximation and its properties *)

  Definition oclos (a : type) (X : Power_set (Indexed closure)) 
  : iRel closure (ty_denot a) := 
    fun k g d => (Ensembles.In _ (bclos (mrel R) X) (k, g)).

  Fixpoint oapprox (a : type) : iRel closure (ty_denot a) :=
    match a as a0 return iRel closure (ty_denot a0) with
        ty_int => fun k g d => exists m h, g = [iconst m, h] /\ d =-= Val m
      | ty_arrow a b => 
        let oapproxc a i g' d := 
            oclos a (fun kg => let (k, g) := kg in oapprox a k g d) i g' d in
        fun k g f =>
          exists c h,
            g = [igrab c, h] /\
            forall i g' d, i <= k ->
              oapproxc a i g' d ->
              oapproxc b i ([c, g' :: h]) (f d)
      | ty_prod a b =>
         let oapproxc a i g' d := 
             oclos a (fun kg => let (k, g) := kg in oapprox a k g d) i g' d in
         fun k g d =>
           let (d0, d1) := d in
           exists c0 c1 h,
             g = [ipair c0 c1, h] /\
             oapproxc a k ([c0, h]) d0 /\
             oapproxc b k ([c1, h]) d1
    end.

  Definition oapprox_set (a : type) (d : ty_denot a) 
  : Power_set (Indexed closure) :=
    fun kg => let (k, g) := kg in oapprox a k g d.

  Definition oapproxc (a : type) : iRel closure (ty_denot a) :=
    fun k g d => oclos a (oapprox_set a d) k g d.
  
  Notation "x '^BOT'" := (bbot (mrel R) x) (at level 28).
  Notation "x '^TOP'" := (btop (mrel R) x) (at level 28).

  Open Scope O_scope.  

  Lemma oapprox_oapproxc:
    forall a d k g, oapprox a d k g -> oapproxc a d k g.
  Proof.
    intros a d k g Q.
    assert (cl := bclos_clos (mrel R)).
    eapply (f_extensive cl).
    auto.
  Qed.
     
  Lemma oapprox_set_bot:
    forall k g,  ~ Ensembles.In _ (oapprox_set ty_int PBot) (k, g).
  Proof.
    intros k g.
    intro P.
    inversion P as [m].
    inversion H as [h [Q0 Q1]].
    eapply (@PBot_incon_eq _ m).
    simpl in *.
    symmetry.
    auto.
  Qed.

  Definition obot (a : type) (X : Power_set (Indexed closure)) 
  : iRel stack (ty_denot a) := 
    fun k g d => (Ensembles.In _ (bbot (mrel R) X) (k, g)).

  Lemma oapprox_set_bot2 :
    forall k s,  In _ (oapprox_set ty_int PBot ^BOT) (k , s).
  Proof.
    intros k s.    
    intros gj P.
    destruct gj as [j g].    
    destruct j.
    simpl. rewrite rel_equiv. 
    apply StepIndexing.zero. exact R. constructor.
    elim oapprox_set_bot with j g. auto.    
  Qed.

  (** Every closure is an approximation with index [0] *)
   Lemma oapproxc_zero:
    forall g a d,
      oapproxc a 0 g d.
  Proof.
    intros g a d.
    intros p Q.
    destruct p as (l, s).
    simpl.
    rewrite rel_equiv.
    eapply StepIndexing.zero. exact R.
    constructor.
  Qed.

  (** Down closed relation *)
  Definition DC {a : type} (r : iRel closure (ty_denot a)) :=
    forall g j k d d', d <= d' -> j <= k -> r k g d -> r j g d'.

  Hint Unfold DC oapprox_set.

  Lemma oapprox_oapproxc_dc:
    forall a, DC (oapprox a) -> DC (oapproxc a).
  Proof.
    intros a dc.
    intros g j k d d' Q0 Q1 P.
    assert (Included _ (oapprox_set a d) (oapprox_set a d')) as L.
    intro p.
    destruct p as [i g'].
    intro H.
    specialize (dc g' i i).
    eapply dc.
    exact Q0.
    reflexivity.
    assumption.
    assert (cl := bclos_clos (mrel R)).
    assert (K' := f_monotonic cl _ _ L).
    eapply K'.
    eapply btop_dc.
    eapply stepI.
    exact P.
    eapply (leP Q1).
  Qed.
  
  Lemma oapprox_dc :
    forall a, DC (oapprox a).
  Proof.
    induction a as [? | a1 Hip a2 Hip2 | a0 Hip a1 Hip1].
    intros g j k d d' R0 R1 P.
    (* int *)
    inversion P as [m Hs].
    inversion Hs as [h [eq1 eq2]].
    exists m.
    exists h.
    split; auto.
    assert ((Val m : natFlat) <= d') as L.
    rewrite <- eq2. auto.
    assert (K := DLle_Val_exists_eq L).
    destruct K as [l [K0 K1]].
    assert (m = l) as U.
    exact K1.
    rewrite U.
    assumption.
    (* arrow *)
    intros g j k f f' R0 R1 P.
    inversion P as [m Hs].
    inversion Hs as [h [Q0 Q1]].
    econstructor.
    exists h.
    split.
    exact Q0.
    intros l g' d Q2 Q3.
    eapply (oapprox_oapproxc_dc Hip2).
    eapply (R0 _).
    reflexivity.
    eapply Q1.
    transitivity j ;
      assumption.
    assumption.
    (* prod *)
    intros g j k d d' Q0 Q1 P.
    destruct d as (d0, d1).
    inversion P as [c0 Hs].
    inversion Hs as [c1 [h [Q2 [Q3 Q4]]]].
    destruct d' as (d'0, d'1).
    econstructor.
    exists c1.
    exists h.
    split.
    exact Q2.
    split.
    eapply (oapprox_oapproxc_dc Hip).
    eapply Q0.
    exact Q1.
    assumption.
    eapply (oapprox_oapproxc_dc Hip1).
    eapply Q0.
    exact Q1.
    assumption.
  Qed.
  
  Corollary oapproxc_dc :
    forall a, DC (oapproxc a).
  Proof.
    intro a.
    eapply oapprox_oapproxc_dc.
    eapply oapprox_dc.
  Qed.

  (* Unused but useful to understand how we discard the infinite stream 
  Lemma oapprox_set_int_bot:
    forall d k g,
      (forall m, d =-= Val m -> In _ (oapprox_set ty_int d ^BOT) (k, g)) ->
      In _ (oapprox_set ty_int d ^BOT) (k, g).
  Proof.
    intros d k s P.
    intros p.
    destruct p as [l g].
    intro L.
    inversion L as [m H].
    destruct H as [h [Q0 Q1]].
    eapply P.
    exact Q1.
    exact L.
  Qed.
*)
  (** * Unfolding the orthogonal operators *)

  Lemma oapproxc_rel_l:
    forall a g d n m s,
      oapproxc a n g d ->
      n <= m ->
      In _ (oapprox_set a d ^BOT) (m, s) ->
      rel R n g s.
  Proof.
    intros a g d n m s oc Q0 Q1.
    assert (L := oc _ Q1).
    simpl in L.
    rewrite (min_l) in L.
    assumption.
    exact (leP Q0).
  Qed.

  Lemma oapproxc_rel_r:
    forall a g d m n s,
      oapproxc a n g d ->
      m <= n ->
      In _ (oapprox_set a d ^BOT) (m, s) ->
      rel R m g s.
  Proof.
    intros a g d m n s oc Q0 Q1.
    assert (L := oc _ Q1).
    simpl in L.
    rewrite (min_r) in L.
    assumption.
    exact (leP Q0).
  Qed.

  (** * Stability of the logical relation *)

  Corollary oapprox_set_mono:
    forall a d d' p, 
      d <= d' -> 
      oapprox_set a d p ->
      oapprox_set a d' p. 
  Proof.
    intros a d d' p J Q.
    destruct p as (k, g).
    eapply oapprox_dc.
    eauto.
    eapply (leqnn k).
    assumption.
  Qed.

  Corollary oapprox_set_same:
    forall a d d',
      d =-= d' ->
      Same_set _ (oapprox_set a d) (oapprox_set a d').
  Proof.
    intros a d d' Q.
    split ;
    intro p ;
    apply oapprox_set_mono ;
    apply Q.
  Qed.
  
  Corollary oapprox_set_dc:
    forall a d, down_closed (oapprox_set a d).
  Proof.
    intros a d.
    unfold down_closed.
    intros g i j P Q.
    eapply oapprox_dc.
    reflexivity.
    apply (le_le Q).
    assumption.
  Qed.

  Corollary oapproxc_stable:
    forall a k g d d',
      oapproxc a k g d ->
      d =-= d' ->
      oapproxc a k g d'.
  Proof.
    intros a k g d d' Q E.
    eapply oapproxc_dc.
    eapply E.
    reflexivity.
    assumption.
  Qed.

  Lemma oapprox_set_bot_same:
    forall a d d',
      d =-= d' ->
      Same_set _ (oapprox_set a d ^BOT) (oapprox_set a d' ^BOT).
  Proof.
    intros a d d' Q.
    eapply bbot_same_morphism.
    eapply oapprox_set_same.
    auto.
  Qed.
  
  (** * A pointwise extension to environments *)

  Inductive oapproxctx (k : nat) : 
    list closure -> forall ctx, ctx_denot ctx -> Prop :=
  | oapproxctx_nil: oapproxctx k List.nil List.nil tt
  | oapproxctx_cons: 
      forall a g d h ctx e, 
        oapproxc a k g d ->
        oapproxctx k h ctx e ->
        oapproxctx k (g :: h) (a :: ctx)%list (e, d).

  Lemma oapproxctx_dc:
   forall k h ctx e,
     oapproxctx k h ctx e ->
     forall l, 
       l <= k ->
       oapproxctx l h ctx e.
  Proof.
    induction 1.
    intros l lk.
    constructor.
    intros l lk.
    constructor.
    eapply oapproxc_dc.
    reflexivity.
    exact lk.
    assumption.
    eauto.
  Qed.
 
  (** Approximation and lookup *)
  Lemma oapproxctx_lookup:
    forall k h ctx e,
      oapproxctx k h ctx e ->
      forall n a,
      forall H : lookup ctx n = Some a,
      exists g,
        lookup h n = Some g /\
        oapproxc a k g (var_denot H e).
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

  Lemma oapproxc_var:
    forall k h ctx e,
      oapproxctx k h ctx e ->
      forall n a,
      forall H : lookup ctx n = Some a,
        oapproxc a k ([iaccess n, h]) (var_denot H e).
  Proof.
    intros k h ctx e Q.
    intros n a H.
    set (L := oapproxctx_lookup Q _ H).
    destruct L as [g [E0 Q1]].
    eapply btop_weakened.
    eapply bbot_dc. exact R.
    intros p.
    destruct p as (l, s).
    intros I lk.
    assert (rel R l g s) as R0.
    eapply oapproxc_rel_l.
    eapply oapproxc_dc.
    reflexivity.
    exact (le_le lk).
    exact Q1.
    reflexivity.
    exact I.
    eapply antiexec_weak.
    exact R0.
    constructor.
    assumption.
  Qed.

  (** * Obtaining tests of different types *)

  (** Tests of arrow types *)
  Lemma oapprox_set_fun:
    forall g k a b d s, 
    forall (f : ty_denot (a ⇾ b)),
      oapproxc a k g d ->
      In _ (oapprox_set b (f d) ^BOT) (k, s) ->
      In _ (oapprox_set (a ⇾ b) f ^BOT) (k, (-[g] :: s)%list).
  Proof.
    intros g k a b d s f P Q.
    eapply (bbot_weakened _).
    apply oapprox_set_dc.
    intros p Q0.
    destruct p as (l, g').
    intro lk.
    inversion Q0 as [c Hs]. 
    inversion Hs as [h [Q1 R0]].
    assert (P' := oapproxc_dc (Ole_refl d) (le_le lk) P).
    specialize (R0 _ _ _ (leqnn l) P').
    eapply antiexec_weak.
    eapply (oapproxc_rel_l R0).
    exact (le_le lk).
    exact Q.
    rewrite Q1.
    constructor.
  Qed.

  (** Tests of product types *)
  Lemma oapprox_set_fst:
    forall a b s d0 d1 h k,
      In _ (oapprox_set a d0 ^BOT) (k, s) ->
      In _ (oapprox_set (a × b) (d0, d1) ^BOT) (k, -[ifst, h] :: s).
  Proof.
    intros a b s d0 d1 h k.
    intro I.
    eapply bbot_weakened.
    eapply oapprox_set_dc.
    intro p.
    destruct p as (l, g).
    intros I1 lk.
    inversion I1 as [c0 Hs].
    inversion Hs as [c1 H].
    destruct H as  [h0 [Q0 [Q1 Q2]]].
    assert (rel R l ([c0, h0]) s) as R0.
    eapply oapproxc_rel_l.
    exact Q1.
    exact (le_le lk).
    exact I.
    eapply antiexec_star_weak.
    rewrite Q0.
    (* star trans *)
    eapply star_step.
    constructor.
    eapply star_one.
    constructor.
    auto.
  Qed.

  Lemma oapprox_set_snd:
    forall a b s d0 d1 h k,
      In _ (oapprox_set b d1 ^BOT) (k, s) ->
      In _ (oapprox_set (a × b) (d0, d1) ^BOT) (k, -[isnd, h] :: s).
  Proof.
    intros a b s d0 d1 h k.
    intro I.
    eapply bbot_weakened.
    eapply oapprox_set_dc.
    intro p.
    destruct p as (l, g).
    intros I1 lk.
    inversion I1 as [c0 Hs].
    inversion Hs as [c1 H].
    destruct H as [h0 [Q0 [Q1 Q2]]].
    assert (rel R l ([c1, h0]) s) as R1.
    eapply oapproxc_rel_l.
    exact Q2.
    exact (le_le lk).
    exact I.
    eapply antiexec_star_weak.
    rewrite Q0.
    (* star trans *)
    eapply star_step.
    constructor.
    eapply star_one.
    constructor.
    auto.
  Qed.

  Lemma oapprox_set_cond:
    forall g k a b d s d0 d1,
      oapproxc ty_int k g d ->
      (d =-= Val 0 -> In _ (oapprox_set a d0 ^BOT) (k, s)) ->
      (forall m, m <> 0 -> d =-= Val m -> In _ (oapprox_set b d1 ^BOT) (k, s)) ->
      In _ (oapprox_set (a × b) (d0, d1) ^BOT) (k, (-[g] :: s)%list).
  Proof.
    intros g k a b d s d0 d1 Q0 P1 P2.
    apply (bbot_weakened _).
    eapply oapprox_set_dc.
    intros p L.
    destruct p as (l, g').
    intro lk.
    inversion L as [c0 Hs].
    destruct Hs as [c1 [h [E0 [Q1 Q2]]]].
    set (g0 := [c0, h]).
    set (g1 := [c1, h]).
    assert (rel R l g (-< g0,  g1 >- :: s )%list) as R0.
    eapply oapproxc_rel_r.
    exact Q0.
    exact (le_le lk). 
    apply (bbot_weakened _).
    eapply oapprox_set_dc.
    intro p.
    destruct p as (j, g'').
    intros L' jl.
    inversion L' as [n Hs].
    inversion Hs as [h' [E3 E2]].
    assert ((j <= k) %coq_nat) as jk.
    transitivity l.
    exact jl. exact lk.
    destruct (eq_nat_dec n 0) as [E4 | E4].
    (* m = 0 *)
    rewrite E4 in E2.
    specialize (P1 E2).
    assert (rel R j g0 s) as R1.
    eapply oapproxc_rel_r.
    exact Q1.
    exact (le_le jl).
    eapply bbot_dc. exact R.
    exact P1.
    exact jk.
    eapply antiexec_weak.
    exact R1.
    rewrite E3.
    rewrite E4.
    constructor.
    (* m <> 0 *)
    specialize (P2 _ E4 E2).
    assert (rel R j g1 s) as R1.
    eapply oapproxc_rel_r.
    exact Q2.
    exact (le_le jl).
    eapply bbot_dc. exact R.
    exact P2.
    exact jk.
    eapply antiexec_weak.
    exact R1.
    rewrite E3.
    econstructor.
    assumption.
    (**)
    eapply antiexec_weak.
    exact R0.
    rewrite E0.
    constructor.
  Qed.

  (* unused *)
  Corollary oapprox_set_cond_zero:
    forall g k a b s d0 d1,
      oapproxc ty_int k g (Val 0) ->
      In _ (oapprox_set a d0 ^BOT) (k, s) ->
      In _ (oapprox_set (a × b) (d0, d1) ^BOT) (k, (-[g] :: s)%list).
  Proof.
    intros g k a b s d0 d1 Q I.
    eapply oapprox_set_cond.
    eapply Q.
    eauto.
    intros m H0 H1.
    set (H := vinj H1).
    clearbody H.
    destruct H as [L0 L1].
    simpl in *.
    rewrite L1 in H0.
    contradict H0.
    auto.
  Qed.

  (* unused *)
  Corollary oapprox_set_cond_non_zero:
    forall g k a b s (d0 : ty_denot a) (d1 : ty_denot b) m,
      oapproxc ty_int k g (Val m) ->
      m <> 0 ->
      In _ (oapprox_set b d1 ^BOT) (k, s) ->
      In _ (oapprox_set (a × b) (d0, d1) ^BOT) (k, (-[g] :: s)%list).
  Proof.
    intros g k a b s d0 d1 m Q H I.
    eapply oapprox_set_cond.
    eapply Q.
    intro Q0.
    set (Q1 := vinj Q0).
    clearbody Q1.
    destruct Q1 as [L0 L1].
    simpl in *.
    rewrite L0 in H.
    contradict H. auto.
    intros.
    auto.
  Qed.

  (** A pointwise extension to lists *)
  Definition oapproxc_all 
             (a : type) (k : nat) (cl : list closure) 
             (dl : list (ty_denot a)) :=
    Forall2 (oapproxc a k) cl dl.

  Lemma oapproxc_all_length:
    forall a k cl dl,
      oapproxc_all a k cl dl ->
      length cl = length dl.
  Proof.
    intros.
    eapply forall2_length.
    eauto.
  Qed.

  Lemma oapproxc_all_dc:
    forall a l k cl dl,
      oapproxc_all a k cl dl ->
      l <= k ->
      oapproxc_all a l cl dl.
  Proof.
    induction 1.
    intros lk.
    constructor.
    intros q.
    econstructor.
    eapply oapproxc_dc ;
    eauto.
    unfold oapproxc_all in *.
    eauto.
  Qed.

  (** Using frames to obtain new tests *)

  Lemma oapprox_set_op:
    forall n (op : operator (S n)),
    forall (cl : list closure),
    forall (dl : list natFlat),
    forall (eargs : list nat),
    forall k,
      oapproxc_all ty_int k cl dl -> 
      forall d s r,
        let fr := stack_val_frame (frame_op _ op eargs cl) in 
        op_fapply_both eargs (d :: dl) op = Some r ->
        In _ (oapprox_set ty_int r ^BOT) (k, s)%list ->
        In _ (oapprox_set ty_int d ^BOT) (k, fr :: s)%list.
   Proof.
     intros n op.
     induction cl as [g | g];
     intros dl eargs k Q d s r fr E0 I.
     (* case cl = nil *)
     assert (dl = nil) as E.
     set (L := oapproxc_all_length Q).
     destruct dl ; simpl in L.
     reflexivity. discriminate.
     subst dl.
     eapply bbot_weakened. apply oapprox_set_dc.
     intro p. destruct p as (l, g).
     intros I1 lk.
     inversion I1 as [v Hs].
     inversion Hs as [h [ E1 E2 ]].
     assert (all_values (d :: nil) (v :: nil)%list) as av.
     econstructor. assumption. constructor.
     set (H := op_fapply_both_values av E0).
     destruct H as [v' [E4 E5]].
     set (g' := [iconst v', h]).
     assert (oapprox ty_int l g' r) as Q1.
     exists v'. exists h.
     split ; trivial.
     assert (rel R l g' s) as R0.
     eapply oapproxc_rel_l.
     eapply oapprox_oapproxc.
     exact Q1. reflexivity.
     eapply bbot_dc. exact R.
     eassumption.
     exact lk.
     eapply antiexec_weak.
     exact R0.
     set (H := op_fapply_list_def E4).
     destruct H as [vec [E6 E7]].
     (* star trans *)
     rewrite E1. unfold g'.
     rewrite <- E7. unfold op_fapply.
     eapply trans_const_full.
     assumption.
     (* case g :: cl *)
     eapply bbot_weakened. apply oapprox_set_dc.
     intro p. destruct p as (l, g').
     intros I1 lk.
     inversion I1 as [v Hs].
     inversion Hs as [h [E1 E2]].
     set (L := oapproxc_all_length Q).
     destruct dl as [ | d' dl'].
     simpl in L. discriminate.
     inversion Q as [H0 | g0 l0 cl0 d'0 Q1 Q2]. subst.
     set (fr0 := stack_val_frame (frame_op _ op (eargs ++ (v :: nil)) cl)).
     assert (In _ (oapprox_set ty_int d' ^BOT) (k, (fr0 :: s)%list)) as Q3.
     set (X := op_fapply_both_step3 E2 E0).
     destruct X as [d1 [X E]].
     eapply IHcl with (r := d1).
     exact Q2. exact X.
     eapply oapprox_set_bot_same.
     symmetry. exact E.
     exact I.
     set (H := le_le lk).
     assert (rel R l g (fr0 :: s)%list) as R0.
     apply oapproxc_rel_l with ty_int d' k.
     eapply oapproxc_dc. reflexivity.
     apply H. auto. auto.
     assert (rel R l g (fr0 :: s)%list) as R0.
     apply oapproxc_rel_l with ty_int d' k.
     eapply oapproxc_dc. reflexivity. 
     apply H. auto. auto. auto. auto.
     eapply antiexec_weak.
     exact R0. constructor.
   Qed.

  (** * Combining approximations *)

  (** Approximation of a functional application *)
  Lemma oapproxc_fun:
    forall c c' h a b k f d,
      oapproxc (a ⇾ b) k ([c, h]) f ->
      oapproxc a k ([c', h]) d ->
      oapproxc b k ([ipush c' c, h]) (f d).
  Proof.
    intros c c' h a b k f d L0 L1.
    apply (btop_weakened _).
    eapply bbot_dc. exact R.
    intros p Q0.
    destruct p as (l, s).
    intro lk.
    assert (L2 := oapproxc_dc (Ole_refl d) (le_le lk) L1).
    assert (Q1 := oapprox_set_fun f L2 Q0).
    eapply antiexec_weak.
    eapply (oapproxc_rel_r L0 (le_le lk) Q1).
    constructor.
  Qed.

  (** Approximation of a fixed-point operator *)
  Lemma oapproxc_fix:
    forall k c h a (f : ty_denot (a ⇾ a)),
      oapproxc (a ⇾ a) k ([c, h]) f ->
      oapproxc a k ([ifix c, h]) (FIXP f).
  Proof.
    induction k ;
    intros c h a f Q.
    eapply oapproxc_zero.
    set (g := [c, h]).
    fold g in Q.
    set (g' := [ifix c, h]).
    set (d  := FIXP f).
    eapply btop_weakened.
    eapply bbot_dc. exact R.
    intro p.
    destruct p as (l, s).
    intros I lSk.
    destruct (le_lt_eq_dec l (S k)) as [H0 | H1]. 
    assumption.
    (* case l <= k *)
    assert ((l <= k) %coq_nat) as H2.
    eapply le_S_n. auto.
    eapply oapproxc_rel_l.
    eapply oapproxc_dc.
    reflexivity.
    exact (le_le H2).
    eapply IHk.
    eapply oapproxc_dc.
    reflexivity.
    exact (leqnSn _).
    exact Q.
    reflexivity.
    exact I.
    (* case l = k+1 *)
    subst l.
    assert (In _ (oapprox_set (a ⇾ a) f ^BOT) (k, -[g'] :: s)) as I1.
    eapply oapprox_set_fun.
    eapply IHk.
    eapply oapproxc_dc.
    reflexivity.
    eapply leqnSn.
    exact Q.
    eapply oapprox_set_bot_same.
    symmetry.
    eapply FIXP_eq.
    eapply bbot_dc. exact R.
    exact I.
    eapply (leP (leqnSn _)).
    assert (rel R k g (-[g'] :: s)) as R0.
    eapply oapproxc_rel_l.
    eapply oapproxc_dc.
    reflexivity.
    eapply leqnSn.
    exact Q.
    reflexivity.
    exact I1.
    eapply antiE.
    exact R0.
    constructor.
  Qed.

  (** Approximation of conditionals *)
  Lemma oapproxc_cond:
    forall c c' h a k d0 d1 d,
      oapproxc (a × a) k ([c, h]) (d0, d1) ->
      oapproxc ty_int k ([c',  h]) d ->
      oapproxc a k ([ipush c' c, h]) (GKL (condc _) d (d0, d1)).
  Proof.
    intros c c' h a k d0 d1 d Q0 Q1.
    fold (ty_denot a) in *.
    eapply btop_weakened.
    eapply bbot_dc. exact R.
    intro p.
    destruct p as (l, s).
    intros L lk.
    set (g := [c , h]). set (g' := [c', h]).
    fold g in Q0. fold g' in Q1.
    assert (oapproxc ty_int l g' d) as Q1'.
    eapply oapproxc_dc.
    exact (Ole_refl d).
    exact (le_le lk).
    exact Q1.
    assert (rel R l g (-[g'] :: s)%list) as R0. 
    eapply oapproxc_rel_r.
    exact Q0.
    exact (le_le lk).
    eapply oapprox_set_cond.
    exact Q1'.
    (* d == Val 0 *)
    intro E0.
    assert (GKL (condc _) d (d0, d1) =-= d0) as E1.
    rewrite (GKL_value _ _ _ _ _ E0).
    simpl.
    reflexivity.
    eapply btop_same_morphism.
    eapply oapprox_set_same.
    symmetry.
    exact E1.
    exact L.
    (* d == Val m, m <> 0 *)
    intros m E1 E2.
    assert (GKL (condc _) d (d0, d1) =-= d1) as E3.
    rewrite (GKL_value _ _ _ _ _ E2).
    destruct m.
    contradict E1. reflexivity.
    simpl. reflexivity.
    eapply btop_same_morphism.
    eapply oapprox_set_same.
    symmetry.
    exact E3.
    exact L.
    (**)
    eapply antiexec_weak.
    exact R0.
    unfold g.
    constructor.
  Qed.

  Lemma oapproxc_cond':
    forall c c' h a k d' d,
      oapproxc (a × a) k ([c, h]) d' ->
      oapproxc ty_int k ([c',  h]) d ->
      oapproxc a k ([ipush c' c, h]) (GKL (condc _) d d').
  Proof.
    intros c c' h a k d' d.
    destruct d' as (d0, d1).
    intros.
    eapply oapproxc_cond ;
    eauto.
  Qed.

  (** Approximation of projections *)
  Lemma oapproxc_fst:
    forall c h a b k d0 d1,
      oapproxc (a × b) k ([c, h]) (d0, d1) ->
      oapproxc a k ([ipush ifst c, h]) d0.
  Proof.
    intros c h a b k d0 d1 Q.
    fold (ty_denot a) in d0.
    fold (ty_denot b) in d1.
    eapply btop_weakened.
    eapply bbot_dc. exact R.
    intros p.
    destruct p as (l, s).
    intros I lk.
    assert (rel R l ([c, h]) (-[ifst, h] :: s)) as R0.
    eapply oapproxc_rel_l.
    eapply oapproxc_dc.
    reflexivity.
    exact (le_le lk).
    exact Q.
    reflexivity.
    eapply oapprox_set_fst.
    auto.
    eapply antiexec_weak.
    exact R0.
    econstructor.
  Qed.

  Lemma oapproxc_snd:
    forall c h a b k d0 d1,
      oapproxc (a × b) k ([c, h]) (d0, d1) ->
      oapproxc b k ([ipush isnd c, h]) d1.
  Proof.
    intros c h a b k d0 d1 Q.
    fold (ty_denot a) in d0.
    fold (ty_denot b) in d1.
    eapply btop_weakened.
    eapply bbot_dc. exact R.
    intros p.
    destruct p as (l, s).
    intros I lk.
    assert (rel R l ([c, h]) (-[isnd, h] :: s)) as R0.
    eapply oapproxc_rel_l.
    eapply oapproxc_dc.
    reflexivity.
    exact (le_le lk).
    exact Q.
    reflexivity.
    eapply oapprox_set_snd.
    auto.
    eapply antiexec_weak.
    exact R0.
    econstructor.
  Qed.

  (** Approximation of fully applied operators *)
  Lemma oapproxc_op:
    forall n (op : operator (S n)),
    forall (cod : list code),
    forall (h : env),
    forall (dl : list natFlat),
    forall k r,
      oapproxc_all ty_int k (insert_env cod h) dl ->
      op_denot_fapply op dl = Some r -> 
      oapproxc ty_int k ([fold_right ipush (iframe _ op) (rev cod) , h]) r.
  Proof.
     intros n op cod h dl k r Q E.
     eapply btop_weakened.
     apply bbot_dc. exact R.
     set (L := op_denot_fapply_length E). 
     clearbody L.
     set (L1 := oapproxc_all_length Q).
     clearbody L1. 
     intros p. destruct p as (l, s).
     intros P lk.
     assert (length cod = length dl) as L2.
     pattern (length dl).
     rewrite <- L1.
     symmetry.
     eapply map_length.
     destruct dl as [ | d0 dl'].
     simpl in L. discriminate.
     destruct cod as [ | c cod'].
     simpl in L. discriminate.
     simpl in Q.
     inversion Q as [H0 | g0 l0 cl0 d'0 Q1 Q2]. subst. 
     set (xs := insert_env cod' h).
     set (fr := stack_val_frame (frame_op _ op List.nil xs)).
     assert (In _ (oapprox_set ty_int d0  ^BOT) (l,  (fr :: s) %list)) as I.
     eapply oapprox_set_op.
     eapply oapproxc_all_dc.
     exact Q2.
     exact (le_le lk).
     unfold op_denot_fapply in E.
     exact E.
     exact P.
     assert (rel R l ([c, h]) (fr :: s)%list) as R0.
     eapply oapproxc_rel_l.
     eapply oapproxc_dc.
     reflexivity.
     exact (le_le lk).
     exact Q1.
     reflexivity.
     assumption.
     eapply antiexec_star_weak with (g1 := [c, h]) (s1 := (fr :: s)%list).
     (* star trans*)
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
     (**)
     exact R0. 
   Qed.

  (** * Approximation of compiled code *)
   
   Definition oapproxc_term ctx a k h e (t : term ctx a) :=
     oapproxc a k ([compile t, h]) ((term_denot t) e).

   Definition oapproxc_term_all ctx a k h e (xs : list (term ctx a)):=
     oapproxc_all a k 
                  (insert_env (map (@compile _ _) xs) h) (term_denot_list xs e).

   Lemma oapproxc_term_all_def:
     forall ctx a,
     forall (xs : list (term ctx a)),
     forall (e : ctx_denot ctx),
     forall k h,
       oapproxctx k h ctx e ->
       Forall (oapproxc_term k h e) xs ->
       oapproxc_term_all k h e xs.
   Proof.
     induction xs ;
     intros e k h octx H.
     constructor.
     unfold oapproxc_term_all.
     simpl.
     econstructor. 
     inversion H. subst. auto.
     eapply IHxs. auto. 
     inversion H. subst. auto.
   Qed.

   (** The compilation of a term is related with its semantics *)
   Lemma correctness_oapprox:
     forall ctx a,
     forall (t : term ctx a),
     forall k h e,
       oapproxctx k h ctx e ->
       oapproxc a k ([compile t, h]) (term_denot t e).
   Proof.
     set (P ctx a t := 
            forall k h e,
              oapproxctx k h ctx e -> 
              oapproxc a k ([compile t, h]) ((term_denot t) e)).
     intros ctx a t.
     fold (P ctx a t).
     generalize ctx a t.
     clear ctx a t.
     apply term_ind2 ;
     unfold P.
     (* abs *)
     intros ctx a b t1 Hip.
     intros k h e Q.
     eapply oapprox_oapproxc.
     econstructor.
     exists h. 
     split.
     simpl. reflexivity.
     intros i g' d ik Q0.
     eapply Hip.
     simpl.
     econstructor.
     exact Q0.
     eapply oapproxctx_dc.
     exact Q.
     exact ik.
     (* app *)
     intros ctx a b t1 t2 Hip1 Hip2.
     intros k h e Q.
     simpl.
     eapply oapproxc_fun ;
     eauto.
     (* var *)
     intros ctx n a H k h e Q.
     simpl.
     eapply oapproxc_var.
     auto.
     (* fix *)
     intros ctx a t Hip.
     intros k h e Q.
     eapply oapproxc_fix.
     eauto.
     (* const *)
     intros ctx m k h e Q. 
     eapply oapprox_oapproxc.
     simpl.
     eexists. eexists.
     split ; reflexivity.
     (* op *)
     intros ctx n op args Hip.
     intros k h e Q.
     rewrite compile_op_fold.
     rewrite map_rev.
     set (cod := map (@compile _ _) (Vector.to_list args)).
     eapply oapproxc_op.
     eapply oapproxc_term_all_def.
     exact Q.
     assert (List.Forall (P ctx ty_int) (to_list args)) as Hip1.
     rewrite <- Forall_Forall.
     exact Hip.
     assert (forall t, List.In t (to_list args) -> P ctx ty_int t) as Hip2.
     rewrite <- Forall_forall. auto.
     unfold P in Hip2.
     rewrite Forall_forall.
     intro t. intro H.
     specialize (Hip2 t H k h e Q).
     assumption.
     eapply op_denot_fapply_terms.   
     (* pair *)
     intros ctx a b t1 t2.
     intros Hip1 Hip2.
     intros k h e Q.
     simpl.  
     eapply oapprox_oapproxc.
     econstructor.
     eexists.
     eexists.
     split.
     reflexivity.
     split.
     eapply Hip1. auto.
     eapply Hip2. eauto.
     (* fst *)
     intros ctx a b t Hip.
     intros k h e Q.
     simpl.
     eapply oapproxc_fst.
     specialize (Hip k h e Q).
     set (d := (term_denot t) e).
     fold d in Hip.
     assert (d = (fst d, snd d)) as H.
     destruct d. simpl. auto.
     rewrite H in Hip.
     eapply Hip.
     (* snd *)
     intros ctx a b t Hip.
     intros k h e Q.
     simpl.
     eapply oapproxc_snd.
     specialize (Hip k h e Q).
     set (d := (term_denot t) e).
     fold d in Hip.
     assert (d = (fst d, snd d)) as H.
     destruct d. simpl. auto.
     rewrite H in Hip.
     eapply Hip.
     (* cond *)
     intros ctx a ti tp.
     intros Hip0 Hip1.
     intros k h e Q.
     unfold compile.
     fold (compile ti).
     fold (compile tp).
     eapply oapproxc_stable.
     eapply oapproxc_cond'.
     specialize (Hip1 k h e Q).
     unfold term_denot in Hip1.
     fold (term_denot tp) in Hip1.
     exact Hip1.
     eapply Hip0.
     exact Q.
     auto.
   Qed.

End OpApprox.

(** * A concrete instance of the set of observations *)

(* We define an instance of RelE:
  count_rel n g s iff  (g, s) executes at least n transition steps *)

Definition count_rel : iRel closure stack :=
  fun n g s => count trans n (g, s).

Lemma stepI_count : StepI (irel_reli count_rel).
Proof.
  constructor.
  split.
  intro. intro. constructor.
  intro p. destruct p as (g, s).
  intro. unfold count_rel.
  unfold In. simpl.
  constructor.
  intro n.
  intro p. destruct p as (g, s).
  intro I.
  eapply count_succ.
  auto.
Qed.

Lemma iantiexec_count : iantiexec count_rel.
Proof.
  intros g0 g1 s0 s1 i.
  intros.
  econstructor.
  eauto. eauto.
Qed.

Definition countE : RelE := @mkrel count_rel stepI_count iantiexec_count.

 (** * Correctness for divergent terms *)

Notation "x '^BOT'" := (bbot (mrel countE) x) (at level 28).
Notation "x '^TOP'" := (btop (mrel countE) x) (at level 28).


Lemma oapproxc_bot_count:
  forall g,
    (forall k, oapproxc countE ty_int k g PBot) ->
    (forall n s, count trans n (g, s)).
Proof.
  intros g F.
  intros n s.
  specialize (F n).
  change (count_rel n g s).
  eapply (@oapproxc_rel_l countE).
  exact F. reflexivity.
  apply oapprox_set_bot2 with (R:=countE).
Qed.

(** A divergent configuration can make an arbitrarily large number of steps *)
Definition infinite_trans (w : conf) : Prop :=
  forall n, count trans n w.

(** Correctness for closed terms of ground types *)
Lemma correctness_int_infinite_trans:
  forall t : term nil ty_int,
    term_denot t tt =-= PBot ->
    forall s, infinite_trans ([compile t, nil], s).
Proof.
  intros t Q s n.
  eapply oapproxc_bot_count.
  intro k.
  apply oapproxc_stable with (d := (term_denot t) tt).
  eapply correctness_oapprox.
  constructor.
  exact Q.
Qed.

(** Coinductive version of divergence **)
Definition diverges (w : conf) : Prop := infseq trans w.

Lemma infinite_trans_step:
  forall w w',
    infinite_trans w ->
    trans w w' ->
    infinite_trans w'.
Proof.
  intros w w' Q T.
  intro n.
  specialize (Q (S n)).
  eapply count_inv.
  eapply trans_deterministic.
  eauto.
  eauto.
Qed.

Lemma infinite_trans_diverges:
  forall w, infinite_trans w -> diverges w.
Proof.
  cofix.
  intros w d1.
  set (d1' := d1).
  clearbody d1'.
  specialize (d1 1).
  inversion d1 as [n | w1 w2 n Q0 Q1 Q2 Q3].
  apply infseq_step with (b := w2).
  auto.
  eapply infinite_trans_diverges.
  eapply infinite_trans_step.
  eauto. eauto.
Qed.

Theorem correctness_int_divergent:
  forall t : term nil ty_int,
    term_denot t tt =-= PBot ->
    forall s, diverges ([compile t, nil], s).
Proof.
  intros t Q s.
  eapply infinite_trans_diverges.
  eapply correctness_int_infinite_trans.
  auto.
Qed.
