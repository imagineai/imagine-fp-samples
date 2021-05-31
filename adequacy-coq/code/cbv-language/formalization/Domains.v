(**********************************************************************************
 * uniirec.v                                                                      *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * July 2010                                                                      *
 * Build with Coq 8.2pl1 plus SSREFLECT                                           *
 **********************************************************************************)

(* Construction of recursive domain for interpreting unityped lambda calculus *)

Add LoadPath "../domain-theory".

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *) 

Require Import Utils.
Require Export PredomAll.
Require Import PredomRec.
Require Import PredomProd.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma kcpoCatAxiom : @Category.axiom
                       cpoType 
                       (fun X Y => exp_cppoType X (liftCppoType Y))
                       (fun X Y Z f g => kleisli f << g) (@eta).
Proof.
  split ; last split ; last split.
  - move => D0 D1 f. simpl. rewrite kleisli_unit. by rewrite comp_idL.
  - move => D0 D1 f. simpl. by rewrite kleisli_eta_com.
  - move => D0 D1 D2 D3 f g h. simpl. rewrite <- kleisli_comp.
      by rewrite comp_assoc.
  - move => D0 D1 D2 f f' g g'. simpl. move => e e'. rewrite e. by rewrite e'.
Qed.
Canonical Structure kcpoCatMixin := CatMixin kcpoCatAxiom.
Canonical Structure kcpoCatType := Eval hnf in CatType kcpoCatMixin.

Module Type RecDom.
  Variable DInf : cpoType.
  
  Definition VInf := discrete_cpoType nat +
                    (DInf -=> DInf _BOT) +
                    (DInf * DInf).
  Variable Roll : VInf =-> DInf.
  Variable Unroll : DInf =-> VInf.

  Variable RU_id : Roll << Unroll =-= Id.
  Variable UR_id : Unroll << Roll =-= Id.

  Definition inBool :=
    in1 (A:=bool_cpoType + nat_cpoType + (DInf -=> DInf _BOT)) (B:=DInf * DInf)
        <<
    in1 (A:=bool_cpoType + nat_cpoType) (B:=DInf -=> DInf _BOT)
        <<
    in1 (A:=bool_cpoType) (B:=nat_cpoType).
    
  Definition inNat : nat_cpoType =-> VInf :=
    in1 (A:=nat_cpoType + (DInf -=> DInf _BOT)) (B:=DInf * DInf)
        <<
    in1 (A:=nat_cpoType) (B:=DInf -=> DInf _BOT).

  Definition inFun : (DInf -=> DInf _BOT) =-> VInf :=
    in1 (A:=nat_cpoType + (DInf -=> DInf _BOT)) (B:=DInf * DInf)
        <<
    in2 (A:=nat_cpoType) (B:=DInf -=> DInf _BOT).
  
  Definition inPair : (DInf * DInf) =-> VInf :=
    in2 (A:=nat_cpoType + (DInf -=> DInf _BOT)) (B:=DInf * DInf).
  
  Variable delta : (DInf -=> DInf _BOT) =-> (DInf -=> DInf _BOT).

  Variable delta_simpl : forall (e : DInf -=> DInf _BOT),
      delta e =-= kleisli (eta << Roll) <<
            [| [| eta << inNat
               , eta << inFun <<
                     ((exp_fun
                         (CCOMP DInf (DInf _BOT) (DInf _BOT):cpoCatType _ _)
                         (kleisli e) : cpoCatType _ _)
                        <<
                        ((exp_fun
                            ((CCOMP DInf (DInf _BOT) (DInf _BOT)) << SWAP)
                            e :cpoCatType _ _) << KLEISLI))
                |]
             , kleisli (eta << inPair) <<
                       uncurry (Smash DInf DInf) << prod_morph (e, e)
             |]
            << Unroll.
  
  Variable delta_eta : delta eta =-= eta.
  Variable id_min : eta =-= @FIXP _ delta.

End RecDom.

Module RD : RecDom.

  Lemma kcpoTerminalAxiom : CatTerminal.axiom (Zero: kcpoCatType).
  Proof.
    simpl. move => D x y. split.
    move => i. simpl. apply: DLless_cond. by case.
    move => i. simpl. apply:DLless_cond. by case.
  Qed.

  Canonical Structure kcpoTermincalCatMixin :=
    @terminalCatMixin kcpoCatType (Zero: kcpoCatType)
                      (fun X => const _ (PBot: (liftCpoPointedType Zero)))
                      kcpoTerminalAxiom.
  Canonical Structure kcpoTerminalCat :=
    Eval hnf in @terminalCatType kcpoCatType kcpoTermincalCatMixin.

  Lemma kcpo_comp_eq (X Y Z : cpoType) m m' :
    ((CCOMP X (Y _BOT) (Z _BOT)) << KLEISLI >< Id) (m,m')
    =-= 
    Category.tcomp kcpoCatMixin m m'.
  Proof.
      by [].
  Qed.

  Definition kcpoBaseCatMixin := CppoECatMixin kcpoTermincalCatMixin kcpo_comp_eq.
  
  (*=kcpoBaseCat *)
  Canonical Structure kcpoBaseCatType := Eval hnf in CppoECatType kcpoBaseCatMixin.
  Lemma leftss : (forall (X Y Z : kcpoBaseCatType) (f : kcpoBaseCatType X Y),
                     (PBot:kcpoCatType _ _) << f =-= (PBot: X =-> Z)).
    (*=End *)
  Proof.
    move => X Y Z f. apply: fmon_eq_intro.
    move => x. split ; last by apply: leastP.
    apply: DLless_cond.
    move => z. move => A.
    case: (kleisliValVal A) => y [_ F]. by case: (PBot_incon_eq (Oeq_sym F)).
  Qed.

  Definition ProjSet (T:Tower kcpoBaseCatType) :=
    fun (d:prodi_cpoType (fun n => tobjects T n _BOT)) => forall n,
        PROJ (fun n => tobjects T n _BOT) n d =-= 
             kleisli (tmorphisms T n) (PROJ (fun n => tobjects T n _BOT) (S n) d) /\ 
        exists n, exists e, PROJ (fun n => tobjects T n _BOT) n d =-= Val e.
  
  Lemma ProjSet_inclusive T : admissible (@ProjSet T).
    move => T. unfold ProjSet. unfold admissible.
    intros c C n.
    split. do 3 rewrite -> lub_comp_eq.
    refine (lub_eq_compat _).
    refine (fmon_eq_intro _).
    intros m. simpl. specialize (C m n). by apply (proj1 C).
    specialize (C 0 0). destruct C as [_ C]. clear n.
    destruct C as [n [e P]].
    exists n.
    assert (forall n, continuous ((PROJ (fun n0 : nat => tobjects T n0 _BOT) n)))
      as Cp by auto.
    assert (PROJ (fun n : nat => tobjects T n _BOT) n (c 0) <=
            PROJ (fun n : nat => tobjects T n _BOT) n (lub c)) as L by
          (apply: fmonotonic ; auto).
    rewrite -> P in L.
    destruct (DLle_Val_exists_eq L) as [dn [Y X]].
    exists dn. by apply Y.
  Qed.

  Definition kcpoCone (T:Tower kcpoBaseCatType) : Cone T.
    move => T. exists (sub_cpoType (@ProjSet_inclusive T))
                (fun i:nat => PROJ _ i << Forget (@ProjSet_inclusive T)).
    move => i. apply: fmon_eq_intro. case => d Pd.
      by apply (Oeq_sym (proj1 (Pd i))).
  Defined.

  Arguments InheritFun [D E P].

  Lemma retract_total D E (f:D =-> E _BOT) (g:E =-> D _BOT) :
    kleisli f << g =-= eta -> total g.
  Proof.
    move => D E f g. unfold total. move => X d. have X':=fmon_eq_elim X d.
    case: (kleisliValVal X'). move => e [Y _]. exists e. by apply Y.
  Qed.

  Lemma xx (T:Tower kcpoBaseCatType) i :
    (forall d : tobjects T i, ProjSet (PRODI_fun (t_nm T i) d)).
  Proof.
    move => T i d n. split. simpl.
      by rewrite -> (fmon_eq_elim (t_nmProjection T i n) d).
      exists i. exists d. simpl. by rewrite t_nn_ID.
  Qed.

  Definition kcpoCocone (T:Tower kcpoBaseCatType) : CoCone T.
    move => T. exists (sub_cpoType (@ProjSet_inclusive T))
                (fun i => eta << @InheritFun _ _ _ (@ProjSet_inclusive T)
                           (PRODI_fun (t_nm T i)) (@xx T i)).
    move => i. rewrite {1} /Category.comp. simpl.
    apply: fmon_eq_intro => d. split.
    - apply: DLless_cond. case => x Px C. case: (kleisliValVal C). clear C.
      move => y [md X].
      apply Ole_trans with (kleisli (eta << InheritFun (@ProjSet_inclusive T)
                                         (PRODI_fun (t_nm T i.+1)) (@xx T _))
                                    (Val y)) ;
        first by rewrite <- md.
      rewrite kleisliVal. rewrite -> X. apply: (fmonotonic (@eta_m _)).
      unfold Ole. simpl.
      move => n. simpl. have Y:=vinj X.
      case: (fmon_stable (Forget (@ProjSet_inclusive T)) Y). clear Y. simpl.
      move => Y Y'.
      specialize (Y' n). rewrite -> Y'.
      rewrite -> (fmon_eq_elim (t_nmEmbedding T i n) d). simpl.
      rewrite -> md. by rewrite kleisliVal.
    - case: (retract_total (proj1 (teppair T i)) d). move => x e.
      apply Ole_trans with (y:=kleisli (eta << InheritFun (@ProjSet_inclusive T)
                                           (PRODI_fun (t_nm T i.+1)) (@xx T _))
                                      (Val x)) ;
        last by rewrite <- e.
      rewrite kleisliVal. apply: DLle_leVal. move => n. simpl.
      apply Ole_trans with (y:=(kleisli (t_nm T i.+1 n) (Val x))) ;
        last by rewrite kleisliVal.
      rewrite <- e. by apply (proj1 (fmon_eq_elim (t_nmEmbedding T i n) d)).
  Defined.

  Lemma limit_def (T:Tower kcpoBaseCatType) (C:Cone T) d n e' :
    mcone C n d =-= Val e' ->
    exists e, lub (chainPE (kcpoCocone T) C) d =-= Val e.
  Proof.
    move => T C d n e' X. simpl.
    have aa:exists e, (fcont_app (chainPE (kcpoCocone T) C) d) n =-= Val e.
    exists (@InheritFun _ _ _ (@ProjSet_inclusive T) (PRODI_fun (t_nm T n))
                   (@xx T n) e').
    apply (@Oeq_trans _ _ (kleisli (eta << InheritFun (@ProjSet_inclusive T)
                                        (PRODI_fun (t_nm T n)) (@xx T _))
                                   (mcone C n d))) ; first by [].
    rewrite -> X. by rewrite kleisliVal.
    case: aa => e aa. case: (chainVallubnVal 1 aa) => x bb. exists x. by apply bb.
  Qed.

(*=kcpoLimit *)
  Definition kcpoLimit (T:Tower kcpoBaseCatType) : Limit T.
    (*=End *)
    move => T. exists (kcpoCone T) (fun C : Cone T => lub (chainPE (@kcpoCocone T) C)).
    move => C n. simpl. split.
    - apply: (Ole_trans _ (comp_le_compat (Ole_refl _)
                                          (le_lub (chainPE (kcpoCocone T) C) n))).
      simpl. rewrite {1} /Category.comp. simpl. rewrite comp_assoc.
      rewrite <- kleisli_comp2.
      rewrite <- comp_assoc. rewrite -> ForgetInherit. rewrite prodi_fun_pi.
      rewrite t_nn_ID. rewrite kleisli_unit.
        by rewrite comp_idL. simpl.
        rewrite {1} / Category.comp. simpl.
        refine (Ole_trans (Oeq_le
                             (PredomCore.comp_lub_eq _
                              (chainPE (kcpoCocone T) C))) _).
        rewrite (lub_lift_left _ n). apply: lub_le => i.
        simpl. rewrite comp_assoc.
        rewrite <- (kleisli_comp2 (InheritFun (@ProjSet_inclusive T)
                                             (PRODI_fun (t_nm T (n + i)))
                                             (@xx T _))
                                 (PROJ (fun n0 : nat => tobjects T n0 _BOT) n <<
                                       Forget (@ProjSet_inclusive T))).
        rewrite <- comp_assoc. rewrite ForgetInherit. rewrite prodi_fun_pi.
          by apply (proj2 ((coneCom_l C (leq_addr i n)))).
    - move => C h X. apply: fmon_eq_intro => d. simpl in h. split.
      + apply: DLless_cond. case => x Px E. case: (proj2 (Px 0)) => n.
        case => y Py. rewrite -> E.
        have A:=(fmon_eq_elim (X n) d).
        have AA:=tset_trans A (fmon_stable (kleisli _) E). clear A.
        have A:=tset_trans AA (kleisliVal _ _). clear AA. simpl in A.
        rewrite -> Py in A.
        case: (limit_def A) => lc e. rewrite -> e. apply: DLle_leVal.
        case: lc e => lc Plc e. unfold Ole. simpl.
        move => i. specialize (X i). have Xi:=fmon_eq_elim X d.
        have Xii: (mcone C i) d =-= (kleisli (PROJ _ i << Forget
                                                   (@ProjSet_inclusive T)) ( h d))
          by apply Xi.
        rewrite -> E in Xii. rewrite -> kleisliVal in Xii. simpl in Xii.
        rewrite <- Xii. clear Xi Xii.
        simpl in e. have aa := Ole_trans (le_lub _ i) (proj1 e). clear e h X E.
        simpl in aa.
        have bb:kleisli (eta << (@InheritFun _ _ _ (@ProjSet_inclusive T)
                                             (PRODI_fun (t_nm T (i)))
                                             (@xx T (i))))
                        ((mcone C i) d) <=
                Val (exist (fun x : forall i : nat, Stream (tobjects T i) => ProjSet x)
                           lc Plc) by apply aa. clear aa.
        apply: DLless_cond => di X. rewrite -> X in bb.
        rewrite -> kleisliVal in bb. rewrite -> X.
        have aa:=vleinj bb. clear bb. unfold Ole in aa. simpl in aa.
        specialize (aa i). simpl in aa.
        rewrite <- aa. by rewrite -> (fmon_eq_elim (t_nn_ID T i) di).
      + simpl. apply: lub_le => n. specialize (X n). have Y:=fmon_eq_elim X d.
        clear X.
        simpl mcone in Y. simpl.
        apply Ole_trans with
            (y:=kleisli (eta << (@InheritFun _ _ _ (@ProjSet_inclusive T)
                                            (PRODI_fun (t_nm T n)) (@xx T n)))
                       ( (mcone C n) d))  ; first by [].
        rewrite -> Y.
        apply Ole_trans with (y:=(kleisli (eta << InheritFun (@ProjSet_inclusive T)
                                              (PRODI_fun (t_nm T n)) (@xx T _))
                                 <<
                                 kleisli (PROJ (fun n0 : nat => tobjects T n0 _BOT) n
                                               << Forget (@ProjSet_inclusive T)))
                                  ( h d)) ; first by [].
        apply: DLless_cond. move => aa X. rewrite -> X.
        case: (kleisliValVal X) => b [P Q]. clear X.
        case: (kleisliValVal P) => hd [P' Q']. rewrite -> P'. apply: DLle_leVal.
        rewrite <- (vinj Q). clear P Q aa h d Y P'. unfold Ole.
        case: hd Q' => x Px Q.
        simpl. simpl in Q. move => i. simpl.
        case: (ltngtP n i).
        * move => l. have a:= comp_eq_compat (tset_refl (t_nm T n i))
                                           (coneCom_l (kcpoCone T) (ltnW l)).
          rewrite -> comp_assoc in a.
          have yy:t_nm T n i << mcone (kcpoCone T) n <= mcone (kcpoCone T) i.
          rewrite -> a.
          rewrite -> (comp_le_compat (proj2 (t_nm_EP T (ltnW l))) (Ole_refl _)).
            by rewrite comp_idL.
          specialize (yy (exist _ x Px)). simpl in yy. rewrite -> Q in yy.
          rewrite -> kleisliVal in yy.
            by apply yy.
        * move => l.
          have a:= (proj2 (fmon_eq_elim (coneCom_l (kcpoCone T) (ltnW l))
                                       (exist _ x Px))).
          simpl in a. have aa:(kleisli ( (t_nm T n i)) (x n)) <= (x i) by apply a.
          rewrite -> Q in aa. rewrite -> kleisliVal in aa. by apply aa.
        * move => e. rewrite <- e. clear i e.
          rewrite -> (proj1 (fmon_eq_elim (t_nn_ID T n) b)). by rewrite -> Q.
Defined.

  Lemma summ_mon (F G : BiFunctor kcpoBaseCatType) X Y Z W :
    monotonic (fun p => [|kleisli (eta << in1) <<
                               (morph F X Y Z W p : (ob F X Z) =-> (ob F Y W)),
                       kleisli (eta << in2) <<
                               (morph G X Y Z W p : (ob G X Z) =-> (ob G Y W))
                      |]).
  Proof.
    move => F G X Y Z W. move => p p' l. simpl.
    unfold sum_fun. simpl. unfold in1. simpl. unfold in2. simpl.
    move => x. simpl. do 2 rewrite -> SUM_fun_simpl. case: x.
    - move => s. simpl. by rewrite -> l.
    - move => s. simpl. by rewrite -> l.
  Qed.

  Definition summ (F G : BiFunctor kcpoBaseCatType) X Y Z W :=
    Eval hnf in mk_fmono (@summ_mon F G X Y Z W).
  
  Lemma sumc (F G : BiFunctor kcpoBaseCatType) X Y Z W :
    continuous (@summ F G X Y Z W).
  Proof.
    move => F G X Y Z W c. simpl. unfold sum_fun. simpl. move => x. simpl.
    rewrite -> SUM_fun_simpl. simpl.
    case:x ; simpl => s.
    - do 2 rewrite lub_comp_eq. simpl. apply lub_le_compat => i.
      simpl. unfold sum_fun. simpl. by rewrite SUM_fun_simpl.
    - do 2 rewrite lub_comp_eq. simpl. apply lub_le_compat => i.
      simpl. unfold sum_fun. simpl. by rewrite SUM_fun_simpl.
  Qed.

  Definition sum_func (F G : BiFunctor kcpoBaseCatType) X Y Z W :=
    Eval hnf in mk_fcont (@sumc F G X Y Z W).

  Lemma sum_func_simpl F G X Y Z W x :
    @sum_func F G X Y Z W x =
    [|kleisli (eta << in1) << (morph F X Y Z W x : (ob F X Z) =-> (ob F Y W)),
      kleisli (eta << in2) << (morph G X Y Z W x : (ob G X Z) =-> (ob G Y W))
     |].
  Proof.
      by [].
  Qed.

(** //////////////////////////////////////// *)
(** Acá arranqué a definir cosas para biProd *)

  Lemma prodm_mon (F G : BiFunctor kcpoBaseCatType) X Y Z W :
    monotonic (fun p : (cppoMorph Y X * cppoMorph Z W) =>
                 uncurry (Smash _ _) <<
                         prodc_morph
                         ((morph F X Y Z W p : (ob F X Z) =-> (ob F Y W)))
                         ((morph G X Y Z W p : (ob G X Z) =-> (ob G Y W)))
              ).
    move => F G X Y Z W. move => p p' l. simpl.
    intros (xz,yz). simpl. by rewrite -> l.
  Qed.

  Definition prodm (F G : BiFunctor kcpoBaseCatType) X Y Z W :=
    Eval hnf in mk_fmono (@prodm_mon F G X Y Z W).

  Lemma prodc (F G : BiFunctor kcpoBaseCatType) X Y Z W :
    continuous (@prodm F G X Y Z W).
  Proof.
    move => F G X Y Z W c. simpl.
    set (uSmash := uncurry (Smash (ob F Y W) (ob G Y W))).
    set (mF := (morph F X Y Z W)).
    set (mG := (morph G X Y Z W)).
    unfold prod_morph. simpl.
    intros (a,b).
    assert (app :
           (uSmash << mF (lub c) >< mG (lub c)) (a, b)
           =-=
           uSmash ((mF (lub c) >< mG (lub c)) (a, b))
         ) by auto.
    rewrite -> app. clear app.
    rewrite -> lub_prod_fun.
    rewrite -> lub_comp_eq.
    simpl. auto.
  Qed.

  Definition prod_func (F G : BiFunctor kcpoBaseCatType) X Y Z W :=
    Eval hnf in mk_fcont (@prodc F G X Y Z W).

  Definition biProd (F G : BiFunctor kcpoBaseCatType) : BiFunctor kcpoBaseCatType.
    move => F G. exists (fun X Y     => (ob F X Y) * (ob G X Y))
                  (fun X Y Z W => @prod_func F G X Y Z W).
    intros T0 T1 T2 T3 T4 T5 f g h k.
    simpl.
    set (uSmash45 := uncurry (Smash (ob F T4 T5) (ob G T4 T5))).
    set (uSmash13 := uncurry (Smash (ob F T1 T3) (ob G T1 T3))).
    split;simpl.
    intros (a,b). simpl.
    repeat rewrite <- morph_comp. simpl.
    set (mF0123 := (morph F T0 T1 T2 T3)).
    set (mG0123 := (morph G T0 T1 T2 T3)).
    set (mF1435 := (morph F T1 T4 T3 T5)).
    set (mG1435 := (morph G T1 T4 T3 T5)).
    set (mF0425 := (morph F T0 T4 T2 T5)).
    set (mG0425 := (morph G T0 T4 T2 T5)).
    setoid_rewrite -> Smash_prop. auto.
    intros (a,b). simpl.
    repeat rewrite <- morph_comp. simpl.
    set (mF0123 := (morph F T0 T1 T2 T3)).
    set (mG0123 := (morph G T0 T1 T2 T3)).
    set (mF1435 := (morph F T1 T4 T3 T5)).
    set (mG1435 := (morph G T1 T4 T3 T5)).
    set (mF0425 := (morph F T0 T4 T2 T5)).
    set (mG0425 := (morph G T0 T4 T2 T5)).
    setoid_rewrite -> Smash_prop. auto.  
    intros T0 T1.
    simpl.
    set (uSmash := uncurry (Smash (ob F T0 T1) (ob G T0 T1))).
    set (mA := (morph F T0 T0 T1 T1)).
    set (mB := (morph G T0 T0 T1 T1)).
    split;simpl.
    intros (a,b). simpl. unfold mA, mB.
    do 2 rewrite -> morph_id. unfold Id; simpl.
    rewrite -> Smash_ValVal. auto.
    intros (a,b). simpl. unfold mA, mB.
    do 2 rewrite -> morph_id. unfold Id; simpl.
    rewrite -> Smash_ValVal. auto.
  Defined.

  Definition biSum (F G : BiFunctor kcpoBaseCatType) : BiFunctor kcpoBaseCatType.
    move => F G. exists (fun X Y => (ob F X Y) + (ob G X Y))
                  (fun X Y Z W => @sum_func F G X Y Z W).
    move => T0 T1 T2 T3 T4 T5 f g h k. simpl.
    apply: (@sum_unique cpoSumCatType).
    - rewrite sum_fun_fst. rewrite {2} / Category.comp. simpl.
      rewrite <- comp_assoc.
      rewrite sum_fun_fst. rewrite comp_assoc.
      setoid_rewrite <- kleisli_comp2. rewrite sum_fun_fst.
      rewrite <- (comp_eq_compat (tset_refl (kleisli (eta << in1)))
                                (@morph_comp _ F T0 T1 T2 T3 T4 T5 f g h k)).
      rewrite {6} /Category.comp. simpl. rewrite comp_assoc.
        by rewrite kleisli_comp.
    - rewrite sum_fun_snd. rewrite {2} / Category.comp. simpl.
      rewrite <- comp_assoc.
      rewrite sum_fun_snd. rewrite comp_assoc.
      setoid_rewrite <- kleisli_comp2. rewrite sum_fun_snd.
      rewrite <- (comp_eq_compat (tset_refl (kleisli (eta << in2)))
                                (@morph_comp _ G T0 T1 T2 T3 T4 T5 f g h k)).
      rewrite {6} /Category.comp. simpl. rewrite comp_assoc.
        by rewrite kleisli_comp.
    - move => T0 T1. simpl. apply: (@sum_unique cpoSumCatType).
      + simpl. rewrite sum_fun_fst.
        rewrite (comp_eq_compat (tset_refl (kleisli (eta << in1)))
                                (morph_id F _ _)).
          by rewrite kleisli_eta_com.
      + simpl. rewrite sum_fun_snd.
        rewrite (comp_eq_compat (tset_refl (kleisli (eta << in2)))
                                (morph_id G _ _)).
          by rewrite kleisli_eta_com.
  Defined.

  Lemma bifunm X Y Z W :
    monotonic (fun (p:@cppoMorph kcpoBaseCatType Y X *
                    @cppoMorph kcpoBaseCatType Z W) => 
                 eta << (exp_fun (CCOMP _ _ _ :cpoCatType _ _)
                                 (kleisli (snd p) : cpoCatType _ _)) <<
                     (exp_fun ((CCOMP _ _ _) << SWAP) (fst p)) << KLEISLI).
  Proof.
    move => X Y Z W p p' l f.
    simpl. apply: DLle_leVal. case: l => l l'. rewrite l.
      by rewrite -> (kleisli_le_compat l').
  Qed.

  Add Parametric Morphism (D:cpoType) : (@Val D)
      with signature (@Ole D: D -> D -> Prop) ++> (@Ole (D _BOT))
        as Val_le_cpo_compat.
    intros.
    apply: DLle_leVal.
    auto.
  Qed.


  Lemma bifunc X Y Z W : continuous (mk_fmono (@bifunm X Y Z W)).
  Proof.
    move => X Y Z W. move => c x. simpl.
    apply Ole_trans with
        (y:=eta (((KLEISLI (lub (pi2 << (c:natO =-> _))):cpoCatType _ _)
                   <<
                   exp_fun (CCOMP _ _ (_ _BOT):cpoCatType _ _)
                   (kleisli x) (lub (pi1 << (c:natO =-> _)))))) ; first by [].
    do 2 rewrite lub_comp_eq. rewrite -> PredomCore.lub_comp_both.
    rewrite lub_comp_eq. by apply lub_le_compat => n.
  Qed.

  Definition bi_fun (X Y Z W : kcpoBaseCatType) :
    (@cppoMorph kcpoBaseCatType Y X * cppoMorph Z W)
      =-> 
      (@cppoMorph kcpoBaseCatType (fcont_cpoType X (Z _BOT))
                  (fcont_cpoType Y (W _BOT)))
    := Eval hnf in mk_fcont (@bifunc X Y Z W).

  Lemma bi_fun_simpl T0 T2 T4 T5 f g x :
    (bi_fun T0 T4 T2 T5) (f,g) x = Val (kleisli g << (kleisli x << f)).
  Proof.
      by [].
  Qed.

  Definition biFun : BiFunctor kcpoBaseCatType.
    exists (fun X Y => fcont_cpoType X (Y _BOT)) (fun X Y Z W => @bi_fun X Y Z W).
    move => T0 T1 T2 T3 T4 T5 f g h k. apply: fmon_eq_intro => x.
    apply Oeq_trans with
        (y:=kleisli ((bi_fun T1 T4 T3 T5) (f, g)) ((bi_fun T0 T1 T2 T3) (h, k) x));
      first by [].
    rewrite bi_fun_simpl. rewrite kleisliVal. rewrite bi_fun_simpl.
    apply Oeq_trans with (y:= (bi_fun T0 T4 T2 T5) (h << f, g << k) x) ;
      last by [].
    rewrite bi_fun_simpl. apply: (fmon_stable eta).
    rewrite <- kleisli_comp. rewrite <- kleisli_comp.
    rewrite {6 8} /Category.comp. simpl.
    rewrite <- kleisli_comp. by repeat rewrite comp_assoc.
    move => X Y. apply: fmon_eq_intro => x. apply: (fmon_stable eta).
    simpl. rewrite kleisli_unit. rewrite comp_idL. by rewrite kleisli_eta_com.
  Defined.

  Definition biVar : BiFunctor kcpoBaseCatType.
    exists (fun X Y => Y) (fun X Y Z W => pi2).
      by [].
        by [].
  Defined.

  Definition biConst (X:kcpoBaseCatType) : BiFunctor kcpoBaseCatType.
    move => D. exists (fun (X Y:kcpoBaseCatType) => D)
                (fun (X Y Z W:kcpoBaseCatType) => const _ eta).
    move => T0 T1 T2 T3 T4 T5 f g h k. simpl. unfold Category.comp. simpl.
    rewrite kleisli_unit. by rewrite comp_idL.
    move => T0 T1. by [].
  Defined.

(*=FS *)
  
  Definition FS := biSum (biSum
                           (biConst (discrete_cpoType nat))
                           biFun
                        )
                        (biProd biVar biVar).
(*=End *)
(*=DInf *)
  Definition DInf : cpoType := @DInf kcpoBaseCatType kcpoLimit FS leftss.
  Definition VInf := discrete_cpoType nat +
                    (DInf -=> DInf _BOT) +
                    (DInf * DInf).
  
  Definition Fold : VInf =-> DInf _BOT := Fold kcpoLimit FS leftss.
  Definition Unfold : DInf =-> VInf _BOT := Unfold kcpoLimit FS leftss.
  (*=End *)
  Lemma FU_iso : kleisli Fold << Unfold =-= eta.
      by apply (FU_id kcpoLimit FS leftss).
  Qed.

  Lemma UF_iso : kleisli Unfold << Fold =-= eta.
      by apply (UF_id kcpoLimit FS leftss).
  Qed.

  Lemma ob X Y : ob FS X Y = discrete_cpoType nat +
                             (X -=> (Y _BOT)) +
                             (Y * Y).
      by simpl.
  Qed.

  (* Lemma morph1 X Y Z W f g x : *)
  (*   morph FS X Y Z W (f,g) (INL _ _ (INL _ _ x)) *)
  (*         =-= *)
  (*   Val (INL _ _ (INL _ _ x)). *)
  (* Proof. *)
  (*   move => X Y Z W f g x. simpl. unfold sum_fun. simpl. unlock SUM_fun. *)
  (*   simpl. by do 2 rewrite kleisliVal. *)
  (* Qed. *)

  (* Lemma morph2 X Y Z W f g x : *)
  (*   morph FS X Y Z W (f,g) (INL _ _ (INR _ _ x)) *)
  (*         =-= *)
  (*   Val (INL _ _ (INR _ _ (kleisli g << (kleisli x << f)))). *)
  (* Proof. *)
  (*   move => X Y Z W f g x. simpl. unfold sum_fun. simpl. unlock SUM_fun. *)
  (*   simpl. rewrite kleisliVal. simpl. rewrite kleisliVal. by simpl. *)
  (* Qed. *)

  Lemma comp_simpl : forall (D1 D2 D3 : cpoType)
                       (f : D2 =-> D3) (g : D1 =-> D2) (x : D1),
      (f << g) x = f (g x).
  Proof. auto. Qed.
  
  (* Lemma morph3 X Y Z W f g x : *)
  (*   morph FS X Y Z W (f,g) (INR _ _ (INR _ _ x)) *)
  (*         =-= *)
  (*         admit. *)
  (* Proof. *)

  (*=Delta *)
  Definition delta : (DInf -=> DInf _BOT) =-> (DInf -=> DInf _BOT)
    := delta kcpoLimit FS leftss.
  (*=End *)

  Lemma eta_mono X Y (f g : X =-> Y) : eta << f =-= eta << g -> f =-= g.
  Proof.
    move => X Y f g A. apply: fmon_eq_intro => x.
    have A':=fmon_eq_elim A x. by apply (vinj A').
  Qed.

  (*=ROLL *)
  Lemma foldT : total Fold. 
    (*CLEAR*)
  Proof.
    move => x. simpl.
    have X:=fmon_eq_elim UF_iso x.
    case: (kleisliValVal X). clear X. move => y [P Q]. exists y. by apply P. 
  Qed.
  (*CLEARED*)
  Lemma unfoldT : total Unfold.  (*CLEAR*)
  Proof.
    move => x. simpl.
    have X:=fmon_eq_elim FU_iso x.
    case: (kleisliValVal X). clear X. move => y [P Q]. exists y. by apply P. 
  Qed. (*CLEARED*)
  Definition Roll : VInf =-> DInf := totalL foldT.
  Definition Unroll : DInf =-> VInf := totalL unfoldT.
  Lemma RU_id : Roll << Unroll =-= Id. (*CLEAR*)
  Proof.
    apply eta_mono.
    have X:=FU_iso.
    have A:eta << Roll =-= Fold by apply totalL_eta.
    rewrite <- A in X. clear A. 
    have A:eta << Unroll =-= Unfold by apply totalL_eta.
    rewrite <- A in X. clear A.
    rewrite -> comp_assoc in X. rewrite -> kleisli_eta_com in X.
    rewrite <- comp_assoc in X. rewrite X. by rewrite comp_idR. 
  Qed. (*CLEARED*)
  
  Lemma UR_id : Unroll << Roll =-= Id. 
    (*=End *)
    (*=End *)
  Proof.
    apply eta_mono.
    have X:=UF_iso.
    have A:eta << Roll =-= Fold by apply totalL_eta.
    rewrite <- A in X. clear A. 
    have A:eta << Unroll =-= Unfold by apply totalL_eta.
    rewrite <- A in X. clear A.
    rewrite -> comp_assoc in X. rewrite -> kleisli_eta_com in X.
    rewrite <- comp_assoc in X. rewrite X. by rewrite comp_idR.
  Qed.

  Definition inBool :=
    in1 (A:=bool_cpoType + nat_cpoType + (DInf -=> DInf _BOT)) (B:=DInf * DInf)
        <<
    in1 (A:=bool_cpoType + nat_cpoType) (B:=DInf -=> DInf _BOT)
        <<
    in1 (A:=bool_cpoType) (B:=nat_cpoType).
    
  Definition inNat : nat_cpoType =-> VInf :=
    in1 (A:=nat_cpoType + (DInf -=> DInf _BOT)) (B:=DInf * DInf)
        <<
    in1 (A:=nat_cpoType) (B:=DInf -=> DInf _BOT).

  Definition inFun : (DInf -=> DInf _BOT) =-> VInf :=
    in1 (A:=nat_cpoType + (DInf -=> DInf _BOT)) (B:=DInf * DInf)
        <<
    in2 (A:=nat_cpoType) (B:=DInf -=> DInf _BOT).
  
  Definition inPair : (DInf * DInf) =-> VInf :=
    in2 (A:=nat_cpoType + (DInf -=> DInf _BOT)) (B:=DInf * DInf).

  Lemma delta_simpl (e:DInf =-> DInf _BOT) :
      delta e =-= kleisli (eta << Roll) <<
            [| [| eta << inNat
               , eta << inFun <<
                     ((exp_fun
                         (CCOMP DInf (DInf _BOT) (DInf _BOT):cpoCatType _ _)
                         (kleisli e) : cpoCatType _ _)
                        <<
                        ((exp_fun
                            ((CCOMP DInf (DInf _BOT) (DInf _BOT)) << SWAP)
                            e :cpoCatType _ _) << KLEISLI))
                |]
             , kleisli (eta << inPair) <<
                       uncurry (Smash DInf DInf) << prod_morph (e, e)
             |]
            << Unroll.
  Proof.
    move => e.
    rewrite (@delta_simpl _ kcpoLimit FS leftss e).
    fold Fold. fold Unfold. fold DInf. simpl.
    rewrite <- comp_assoc.
    rewrite {1 2} /Category.comp. simpl.
    have A:eta << Unroll =-= Unfold by apply totalL_eta.
    rewrite <- A. rewrite (comp_assoc Unroll eta). rewrite kleisli_eta_com.
    rewrite comp_assoc. apply: (comp_eq_compat _ (tset_refl Unroll)).
    have B:eta << Roll =-= Fold by apply totalL_eta.
    rewrite <- B. apply comp_eq_compat. auto.
    apply sum_unique. apply sum_unique.
    - Case "Nat".
      do 2 rewrite sum_fun_fst.
      repeat rewrite -> kleisli_eta_com. rewrite sum_fun_fst.
      rewrite <- comp_assoc with (f:=in1 (A:=nat_cpoType) (B:=DInf -=> DInf _BOT)).
      rewrite sum_fun_fst. rewrite -> comp_assoc.
      rewrite <- comp_assoc. rewrite -> comp_assoc.
      rewrite -> kleisli_eta_com. unfold inNat. by repeat rewrite -> comp_assoc.
    - Case "Fun".
      rewrite sum_fun_fst. rewrite sum_fun_snd.
      repeat rewrite -> kleisli_eta_com. rewrite sum_fun_fst.
      rewrite <- comp_assoc with (f:=in2 (B:=DInf -=> DInf _BOT)).
      rewrite sum_fun_snd. rewrite -> comp_assoc. rewrite <- kleisli_comp2.
      unfold inFun.
      repeat rewrite -> comp_assoc. by rewrite -> kleisli_eta_com.
    - Case "Pair".
      rewrite sum_fun_snd. rewrite -> kleisli_eta_com. rewrite sum_fun_snd.
      unfold inPair. by rewrite -> comp_assoc.
  Qed.

  (*=minimal *)
  Lemma id_min : eta =-= FIXP delta.
    (*=End *)
  Proof.
    apply tset_sym. rewrite <- (id_min kcpoLimit FS leftss). fold delta.
    simpl. apply:fmon_eq_intro => n. simpl. apply lub_eq_compat.
      by apply fmon_eq_intro => m.
  Qed.

  Lemma delta_eta : delta eta =-= eta.
      by apply (delta_id_id kcpoLimit FS leftss).
  Qed.

End RD.