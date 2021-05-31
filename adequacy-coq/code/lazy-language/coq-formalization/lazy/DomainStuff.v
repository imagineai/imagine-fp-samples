
Add LoadPath "../denot/domain-theory".
(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

Require Import Utils.
Require Import uniirec.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.

Definition KR := kleisli (eta << Roll).
Definition KUR := kleisli (eta << Unroll).

Canonical Structure int_cpoType := Eval hnf in discrete_cpoType Z.

Lemma EpsStable (D : cpoType) a b : (a =-= b ) -> (@tset_eq (D _BOT) (Eps a) (Eps b)). 
Proof.
  intros D a b [leq geq]. 
  simpl in *.
  split.
  apply DLleEps_left.
  apply DLle_trans with (y := b).
  apply leq.
  apply (fst (eq_Eps b)).
  apply DLleEps_right; apply DLle_trans with (y:=b).
  apply (snd (eq_Eps b)).
  apply geq.
Qed.    

Lemma DLleEpsTrans (D : cpoType) (a b :D _BOT) : a <= b -> Eps a <= b.
Proof.
  intros D a b leq.
  apply DLle_trans with (y := a).
  apply (snd (eq_Eps a)).  apply leq.
Qed. 

Lemma DLleEq (D : cpoType) : forall a b c, a =-= b -> @DLle D a c -> @DLle D b c.
Proof.
  intros D a b c [_ bLta] leq.
  apply (DLle_trans bLta leq).
Qed.  

Lemma DLleEqR (D : cpoType) : forall a c d, c =-= d -> @DLle D a c -> @DLle D a d.
Proof.
  intros D a c d [cLtd _] leq.
  apply (DLle_trans leq cLtd  ). 
Qed.  

Lemma comp_simpl : forall (D1 D2 D3 : cpoType)
                           (f : D2 =-> D3) (g : D1 =-> D2) (x : D1),
    (f << g) x = f (g x).
Proof. auto. Qed.

Lemma prod_simpl : forall (D1 D2 D3 : cpoType)
                     (f : cpoCatType D1 D2) (g : cpoCatType D1 D3) (x : D1),
    (<| f , g |>) x =-= (f x , g x).
Proof.
  by reflexivity.
Qed.

Lemma URid : forall (x : VInf), Unroll (Roll x) =-= x.
Proof.
  intros x. rewrite <- comp_simpl.
  rewrite UR_id. by unfold Id; simpl; unfold id.
Qed.

Lemma RUid : forall (x : DInf), Roll (Unroll x) =-= x.
Proof.
  intros x. rewrite <- comp_simpl.
  rewrite RU_id. by unfold Id; simpl; unfold id.
Qed.

Lemma KLEISLIR_unit2 : forall (D E F : cpoType)
                         (f : (D * E) =-> (F _BOT))
                         (a : D) (b : E),
    (KLEISLIR f) (a, eta b) =-= f (a, b).
Proof.
  intros D E F f a b.
  unfold KLEISLIR. unlock.
  simpl. unfold id, Smash.
  rewrite Operator2_simpl.
  by rewrite kleisliVal.
Qed.

Lemma KLEISLIL_unit2 : forall (D E F : cpoType)
                         (f : (D * E) =-> (F _BOT))
                         (a : D) (b : E),
    (KLEISLIL f) (eta a, b) =-= f (a, b).
Proof.
  intros D E F f a b.
  unfold KLEISLIL. unlock.
  simpl. unfold id, Smash.
  rewrite Operator2_simpl.
  by rewrite kleisliVal.
Qed.

Lemma KLEISLIL_PBot : forall (D E F : cpoType)
                         (f : (D * E) =-> (F _BOT))
                         (b : E),
    (KLEISLIL f) (PBot, b) =-= PBot.
Proof.
  intros D E F f b.
  unfold KLEISLIL. unlock.
  simpl. unfold id, Smash.
  unfold Operator2. unlock.
  simpl. by do 3 rewrite kleisli_bot.
Qed.  

Lemma KLEISLIR_PBot : forall (D E F : cpoType)
                         (f : (D * E) =-> (F _BOT))
                         (a : D),
    (KLEISLIR f) (a, PBot) =-= PBot.
Proof.
  intros D E F f a.
  unfold KLEISLIR. unlock.
  simpl. unfold id, Smash.
  unfold Operator2. unlock.
  simpl. do 2 rewrite kleisliVal. simpl. by do 2 rewrite kleisli_bot.
Qed.

Lemma KLEISLI_LR_Val : forall (A B C : cpoType)
                         (f : (A * B) =-> (C _BOT))
                         (a : A _BOT) (b : B),
    (KLEISLIL (KLEISLIR f)) (a, eta b) =-= (KLEISLIL f) (a, b).
Proof.
  intros A B C f a b.
  apply KLEISLIL_eq.
  intros aa aa' H H0.
  rewrite KLEISLIR_unit2. rewrite -> H in H0.
  apply vinj with (D:=A) in H0. by rewrite H0.
  intros aa H.
  exists aa. apply H.
  intros aa' H.
  exists aa'. apply H.
Qed.

Lemma KLEISLI_RL_Val : forall (A B C : cpoType)
                         (f : (A * B) =-> (C _BOT))
                         (a : A) (b : B _BOT),
    (KLEISLIR (KLEISLIL f)) (eta a, b) =-= (KLEISLIR f) (a, b).
Proof.
  intros A B C f a b.
  apply KLEISLIR_eq.
  intros bb bb' H H0.
  rewrite KLEISLIL_unit2. rewrite -> H in H0.
  apply vinj with (D:=B) in H0. by rewrite H0.
  intros bb H.
  exists bb. apply H.
  intros bb' H.
  exists bb'. apply H.
Qed.

Lemma KLESILIL_lub_comp_eq :
  forall (A B C : cpoType) (f : (A * B) =-> C _BOT) (xi : natO -=> A _BOT) (y : B),
    (KLEISLIL f) (lub xi, y) =-= lub (ocomp (kleisli f)
                                            (ocomp (RStrength _ _)
                                                   (<| xi, fmon_cte _ y |>))).
Proof.
  intros A B C f xi y.
  unfold KLEISLIL. unlock. simpl. unfold id.
  rewrite lub_comp_eq. simpl.
  rewrite lub_comp_eq.
  apply lub_eq_compat.
  auto.
Qed.

Lemma KLESILIR_lub_comp_eq :
  forall (A B C : cpoType) (f : (A * B) =-> C _BOT) (yi : natO -=> B _BOT) (x : A),
    (KLEISLIR f) (x,lub yi) =-= lub (ocomp (kleisli f)
                                            (ocomp (LStrength _ _)
                                                   (<| fmon_cte _ x, yi |>))).
Proof.
  intros A B C f yi x.
  unfold KLEISLIR. unlock. simpl. unfold id.
  rewrite lub_comp_eq. simpl.
  rewrite lub_comp_eq.
  apply lub_eq_compat.
  auto.
Qed.



Definition IfZSemNat (A : Type) (a a' : A) (n : nat_cpoType) : A :=
  match n with
  | O   => a
  | S _ => a'
  end
.

Definition IfZSemInt (A : Type) (a a' : A) (z : int_cpoType) :=
  match z with
  | 0%Z => a
  | _   => a'
  end.

Lemma IfZNatCore_mon
      (A B : ordType) :
      monotonic (fun p : (A -=> B) * (A -=> B) * A * discrete_ordType nat =>
                   (IfZSemNat (fst (fst (fst p))) (snd (fst (fst p))) (snd p))
                     (snd (fst p))
                ).
Proof.
  intros A B.
  intros x y leq.
  destruct x as [[[? ?] ?] ?]. simpl.
  destruct y as [[[? ?] ?] ?]. simpl.
  inversion leq as [[[? ?] ?] ?]. simpl in *.
  have eq : s2 = s6 by [].
  rewrite -> eq.
  destruct s6.
  simpl. apply fmon_le_compat. apply H. apply H1.
  simpl. apply fmon_le_compat. apply H0. apply H1.
Qed.

Lemma IfZIntCore_mon
      (A B : ordType) :
      monotonic (fun p : (A -=> B) * (A -=> B) * A * discrete_ordType Z =>
                   (IfZSemInt (fst (fst (fst p))) (snd (fst (fst p))) (snd p))
                     (snd (fst p))
                ).
Proof.
  intros A B.
  intros x y leq.
  destruct x as [[[? ?] ?] ?]. simpl.
  destruct y as [[[? ?] ?] ?]. simpl.
  inversion leq as [[[? ?] ?] ?]. simpl in *.
  have eq : s2 = s6 by [].
  rewrite -> eq.
  destruct s6.
  simpl. apply fmon_le_compat. apply H. apply H1.
  simpl. apply fmon_le_compat. apply H0. apply H1.
  simpl. apply fmon_le_compat. apply H0. apply H1.
Qed.

Definition IfZNatCoreM (A B : ordType) :
  ((A -=> B) * (A -=> B) * A * discrete_ordType nat) =-> B
  := Eval hnf in mk_fmono (@IfZNatCore_mon A B).

Definition IfZIntCoreM (A B : ordType) :
  ((A -=> B) * (A -=> B) * A * discrete_ordType Z) =-> B
  := Eval hnf in mk_fmono (@IfZIntCore_mon A B).

Lemma IfZNatCore_mon2
      (A B : cpoType) :
      monotonic (fun p : (A -=> B) * (A -=> B) * discrete_cpoType nat =>
                   IfZSemNat (fst (fst p)) (snd (fst p)) (snd p)
                ).
Proof.
  intros A B.
  intros x y leq.
  destruct x as [[? ?] n]. simpl.
  destruct y as [[? ?] n']. simpl.
  inversion leq as [[? ?] ?]. simpl in *.
  have eq : n = n' by [].
  rewrite <- eq.
  destruct n.
  simpl. apply H.
  simpl. apply H0.
Qed.

Lemma IfZIntCore_mon2
      (A B : cpoType) :
      monotonic (fun p : (A -=> B) * (A -=> B) * discrete_cpoType Z =>
                   IfZSemInt (fst (fst p)) (snd (fst p)) (snd p)
                ).
Proof.
  intros A B.
  intros x y leq.
  destruct x as [[? ?] n]. simpl.
  destruct y as [[? ?] n']. simpl.
  inversion leq as [[? ?] ?]. simpl in *.
  have eq : n = n' by [].
  rewrite <- eq.
  destruct n.
  simpl. apply H.
  simpl. apply H0.
  simpl. apply H0.
Qed.

Definition IfZNatCoreM2 (A B : cpoType)
  := Eval hnf in mk_fmono (@IfZNatCore_mon2 A B).

Definition IfZIntCoreM2 (A B : cpoType)
  := Eval hnf in mk_fmono (@IfZIntCore_mon2 A B).

Lemma lub_discrete_chain : forall (A : cpoType) (f : natO =-> discrete_cpoType A)
                             (n : A),
    lub f =-= n -> forall i, f i =-= n.
Proof.
  intros A f n H i.
  rewrite <- H.
  assert (f i <= lub f).
  apply le_lub.
  inversion H0.
  by rewrite H2.
Qed.

Lemma IfZNatCore_cont2 (A B : cpoType) :
  continuous (@IfZNatCoreM2 A B).
Proof.
  intros A B.
  intros x.
  simpl.
  destruct (lub (pi2 << x)) eqn:H.
  simpl.
  apply lub_le_compat.
  apply Oeq_le.
  apply fmon_eq_intro.
  intros n.
  simpl.
  apply Oeq_refl_eq in H.
  eapply lub_discrete_chain with (i:=n) (f := pi2 << x) in H.
  simpl in H.
  inversion H. inversion H0.
  rewrite H3. by simpl.
  simpl.
  apply lub_le_compat.
  apply Oeq_le.
  apply fmon_eq_intro.
  intros n.
  simpl.
  apply Oeq_refl_eq in H.
  eapply lub_discrete_chain with (i:=n) (f := pi2 << x) in H.
  simpl in H.
  inversion H. inversion H0.
  rewrite H3. by simpl.
Qed.  

Lemma IfZIntCore_cont2 (A B : cpoType) :
  continuous (@IfZIntCoreM2 A B).
Proof.
  intros A B.
  intros x.
  simpl.
  destruct (lub (pi2 << x)) eqn:H.
  simpl.
  apply lub_le_compat.
  apply Oeq_le.
  apply fmon_eq_intro.
  intros n.
  simpl.
  apply Oeq_refl_eq in H.
  eapply lub_discrete_chain with (i:=n) (f := pi2 << x) in H.
  simpl in H.
  inversion H. inversion H0.
  rewrite H3. by simpl.
  simpl.
  apply lub_le_compat.
  apply Oeq_le.
  apply fmon_eq_intro.
  intros n.
  simpl.
  apply Oeq_refl_eq in H.
  eapply lub_discrete_chain with (i:=n) (f := pi2 << x) in H.
  simpl in H.
  inversion H. inversion H0.
  rewrite H3. by simpl.
  simpl.
  apply lub_le_compat.
  apply Oeq_le.
  apply fmon_eq_intro.
  intros n.
  simpl.
  apply Oeq_refl_eq in H.
  eapply lub_discrete_chain with (i:=n) (f := pi2 << x) in H.
  simpl in H.
  inversion H. inversion H0.
  rewrite H3. by simpl.
Qed.

Definition IfZNat (A B : cpoType)
  := Eval hnf in mk_fcont (@IfZNatCore_cont2 A B).

Definition IfZInt (A B : cpoType)
  := Eval hnf in mk_fcont (@IfZIntCore_cont2 A B).

(* Unary OP *)
Lemma SimpleU_mon (A :Type) (B:ordType) (op : A -> B:Type) :
  monotonic (fun a:discrete_ordType A => op a).
Proof.
  move => A B op. intros x y H.
  have e:x = y by []. by rewrite e.
Qed.

Lemma SimpleB_mon (A B :Type) (C:ordType) (op : A -> B -> C:Type) : monotonic (fun p:discrete_ordType A * discrete_ordType B => op (fst p) (snd p)).
move => A B C op. case => x0 y0. case => x1 y1. case ; simpl. move => L L'.
have e:x0 = x1 by []. have e':y0 = y1 by []. rewrite e. by rewrite e'.
Qed. 

Definition SimpleBOpm (A B :Type) (C:ordType) (op : A -> B -> C:Type) :
  discrete_ordType A * discrete_ordType B =-> C :=
  Eval hnf in mk_fmono (SimpleB_mon op).

Lemma SimpleB_cont (A B:Type) (C:cpoType) (op : A -> B -> C:Type) :
  @continuous (discrete_cpoType A * discrete_cpoType B) C (SimpleBOpm op).
Proof.
  move => A B C op.
  move => c. simpl. apply: (Ole_trans _ (le_lub _ 0)). simpl.
    by [].
Qed.

Definition SimpleBOp (A B:Type) (C:cpoType) (op : A -> B -> C:Type) :
  discrete_cpoType A * discrete_cpoType B =-> C :=
  Eval hnf in mk_fcont (SimpleB_cont op).

Definition OpPlus : discrete_cpoType nat * discrete_cpoType nat
                    =->
                    discrete_cpoType nat
  := SimpleBOp Peano.plus.
(* Unary OP *)

Lemma Operator2_strictL A B C (f:A * B =-> C _BOT) d :
  Operator2 f PBot d =-= PBot.
Proof.
  move => A B C f d. apply Ole_antisym ; last by apply: leastP.
  unlock Operator2. simpl. by do 2 rewrite kleisli_bot.
Qed.

Lemma Operator2_strictR A B C (f:A * B =-> C _BOT) d :
  Operator2 f d PBot =-= PBot.
Proof.
  move => A B C f d. apply: Ole_antisym ; last by apply: leastP.
  unlock Operator2. simpl.
  apply: (Ole_trans (proj2 (fmon_eq_elim (kleisli_comp2 _ _) d))).
  apply: DLless_cond. move => c X.
  case: (kleisliValVal X) => a [e P]. rewrite -> e. clear d e X.
  simpl in P. rewrite -> kleisli_bot in P.
    by case: (PBot_incon (proj2 P)).
Qed.


Lemma Curry1_mon (D0 D1 D2 : cpoType) : monotonic (@exp_fun cpoExpType D0 D1 D2).
Proof.
  intros D0 D1 D2 x x' l d0 d1. simpl. by rewrite -> l.
Qed.

Definition CURRY1_mon (D0 D1 D2 : cpoType) :=
  Eval hnf in mk_fmono (@Curry1_mon D0 D1 D2).

Lemma Curry1_cont (D0 D1 D2 : cpoType) : continuous (@CURRY1_mon D0 D1 D2).
Proof.
  intros D1 D2 D3 f c x. simpl.
  apply lub_le_compat.
  repeat rewrite fcont_app_eq.
  simpl. intro n. by simpl.
Qed.

Definition CCURRY (D0 D1 D2 : cpoType) :=
  Eval hnf in mk_fcont (@Curry1_cont D0 D1 D2).
Arguments CCURRY [D0 D1 D2].

Lemma UnCurry_mon (D0 D1 D2 : cpoType) :
  monotonic (@uncurry cpoExpType D0 D1 D2).
Proof.
  intros D0 D1 D2 x x' l a.
  simpl.
  apply fcont_le_compat. apply fcont_le_compat. apply l.
  apply Ole_refl. apply Ole_refl.
Qed.

Definition UNCURRY_mon (D0 D1 D2 : cpoType) :=
  Eval hnf in mk_fmono (@UnCurry_mon D0 D1 D2).

Lemma UnCurry_cont (D0 D1 D2 : cpoType) : continuous (@UNCURRY_mon D0 D1 D2).
Proof.
  intros D1 D2 D3 f c.
  simpl.
  apply lub_le_compat.
  repeat rewrite fcont_app_eq.
  simpl. intro n. by simpl.
Qed.

Definition UNCURRY (D0 D1 D2 : cpoType) :=
  Eval hnf in mk_fcont (@UnCurry_cont D0 D1 D2).
Arguments UNCURRY [D0 D1 D2].

Lemma Smash_Eps_l :
  forall (A B : cpoType) (d : A _BOT) (d' : B _BOT),
    (Smash A B) (Eps d) d' = Eps ((Smash A B) d d').
Proof.
  intros A B d d'.
  unfold Smash. unfold Operator2. unlock. simpl.
  do 2 rewrite kleisli_simpl. do 2 rewrite kleisli_Eps.
  by do 2 rewrite <- kleisli_simpl.
Qed.

Definition Operator2_reverse := fun A B C (F: A * B =-> C _BOT) =>
  locked (exp_fun
      (uncurry ((Application _ _) << (kleisli (eta << (exp_fun F)))) << SWAP)).

Definition Smash_reverse := fun A B => @Operator2_reverse _ _ (A * B) eta.

Lemma Smashs_eq :
  forall (A B : cpoType) (d : A _BOT) (d' : B _BOT),
    (Smash A B) d d' = (Smash_reverse A B) d' d.
Proof.
  intros A B d d'.
  unfold Smash, Smash_reverse. unfold Operator2, Operator2_reverse.
  unlock. by simpl.
Qed.

Lemma Smash_Eps_r :
  forall (A B : cpoType) (d : A _BOT) (d' : B _BOT),
    (Smash A B) d (Eps d') = Eps ((Smash A B) d d').
Proof.
Abort.

Lemma KRKUR_id : forall (y : DInf _BOT), KR (KUR y) =-= y.
Proof.
  intros y. unfold KR, KUR.
  rewrite <- comp_simpl.
  setoid_rewrite <- kleisli_comp2.
  rewrite <- comp_assoc.
  rewrite RU_id. rewrite comp_idR.
  rewrite kleisli_unit.
    by simpl.
Qed.

Lemma KURKR_id : forall (y : VInf _BOT), KUR (KR y) =-= y.
Proof.
  intros y. unfold KR, KUR.
  rewrite <- comp_simpl.
  rewrite <- kleisli_comp2.
  rewrite <- comp_assoc.
  rewrite UR_id. rewrite comp_idR.
  rewrite kleisli_unit.
    by simpl.
Qed.

Lemma KRKUR_id2 : forall (A : cpoType) (y : A =-> DInf _BOT), KR << KUR << y =-= y.
Proof.
  intros A y. apply fmon_eq_intro. intro a.
  simpl. apply KRKUR_id.
Qed.

Lemma KURKR_id2 : forall (A : cpoType) (y : A =-> VInf _BOT), KUR << KR << y =-= y.
Proof.
  intros A y. apply fmon_eq_intro. intro a.
  simpl. apply KURKR_id.
Qed.

Lemma KLEISLIR_KR_eq : forall (A : cpoType)
                      (a : A) (b : VInf _BOT) (f : A * VInf =-> VInf _BOT), 
    (KLEISLIR (KR << f)) (a, b) =-= KR ((KLEISLIR (f << Id >< Unroll)) (a, KR b)).
Proof.
  intros A a b f.
  unfold KR, KLEISLIR. unlock. simpl. unfold id.
  unfold Smash. unfold Operator2. unlock. simpl.
  do 4 rewrite kleisliVal. simpl.
  rewrite <- comp_simpl. rewrite <- kleisli_comp2.
  rewrite <- comp_simpl. rewrite <- comp_simpl.
  do 2 rewrite <- comp_assoc. rewrite <- kleisli_comp2.
  rewrite <- comp_simpl. rewrite <- comp_assoc.
  rewrite <- kleisli_comp2. rewrite <- kleisli_comp.
  simpl. apply fmon_eq_compat. reflexivity.
  assert (f << PAIR VInf a
            =-=
          ((f << Id >< Unroll) << PAIR DInf a) << Roll
         ).
  apply fmon_eq_intro. intro d. simpl; unfold id. by rewrite URid.
  by rewrite H.
Qed.

Lemma KLEISLIR_KR_eq2 : forall (A : cpoType) (f : A * VInf =-> VInf _BOT),
    KR << KLEISLIR f =-= KLEISLIR (KR << f).
Proof.
  intros A f. unfold KR, KLEISLIR. unlock.
  rewrite comp_assoc. by rewrite kleisli_comp.
Qed.

Lemma Smash_Val : forall (A B : cpoType) (a : A) (b : B _BOT),
    (Smash A B) (Val a) b = (kleisli (eta << PAIR B a)) b.
Proof.
  intros A B a b.
  unfold Smash. unfold Operator2. unlock. simpl.
  do 2 rewrite kleisli_simpl. repeat rewrite kleisli_Val. by simpl.
Qed.

Lemma KLEISLIR_Eps : forall (A B C : cpoType) (a : A) (b : B _BOT)
                       (f : A * B -=> C _BOT),
    (KLEISLIR f) (a, Eps b) = Eps ((KLEISLIR f) (a, b)).
Proof.
  intros A B C a b f. unfold KLEISLIR. unlock. simpl.
  do 2 rewrite Smash_Val.
  do 4 rewrite kleisli_simpl. unfold id. do 2 rewrite kleisli_Eps. auto.
Qed.

Lemma KLEISLIL_Eps : forall (A B C : cpoType) (a : A _BOT) (b : B)
                       (f : A * B -=> C _BOT),
    (KLEISLIL f) (Eps a, b) = Eps ((KLEISLIL f) (a, b)).
Proof.
  intros A B C a b f. unfold KLEISLIL. unlock. simpl. unfold id.
  rewrite Smash_Eps_l. rewrite kleisli_simpl. rewrite kleisli_Eps.
  by rewrite <- kleisli_simpl.
Qed.

Lemma Smash_ValVal : forall (A B : cpoType) (a : A) (b : B),
    Smash _ _ (Val a) (Val b) =-= Val (a, b).
Proof.
  intros A B a b.
  unfold Smash, Operator2. unlock. simpl.
  rewrite -> kleisliVal. simpl. rewrite -> kleisliVal.
  simpl. rewrite -> kleisliVal. by simpl.
Qed.

Fixpoint FChainCore (A B : cpoType) (n : natO) :
  (B -=> A _BOT -=> A _BOT)
  *
  B =-> A _BOT
  :=
  match n with 
  | O   => const _ PBot
  | S m => ev << <| ev, FChainCore A B m |>
  end.

Definition SwapArgs (A B C : cpoType) : (A * B -=> C) =-> (B * A -=> C)
  := exp_fun(ev << Id >< SWAP).
Arguments SwapArgs [A B C].

Definition FixF (A B : cpoType) :
  (A _BOT * B -=> A _BOT) =-> (B -=> A _BOT)
  := CURRY (ccomp FIXP (UNCURRY ((@CCURRY _ _ _)))) << SwapArgs.
Arguments FixF [A B].

Definition FChain (A B : cpoType) (n : natO) :
  (A _BOT * B) -=> A _BOT
  =->
  (B -=> A _BOT)
  := exp_fun (FChainCore A B n)
  << @CCURRY B (A _BOT) (A _BOT)
  << SwapArgs.

Lemma FChainCore_unfold: forall (A B : cpoType) (n : natO),
    FChainCore A B (n.+1)%N =-= ev << <| ev , FChainCore A B n |> .
Proof. auto. Qed.

Lemma FChainCore_S_unfold: forall (A B : cpoType) (n : natO)
                             (d : B -=> A _BOT -=> A _BOT)
                             (η : B),
    FChainCore A B n (d,η) <= (d η) (FChainCore A B n (d,η)).
Proof.
  intros A B n d η.
  induction n.
  simpl. apply leastP.
  simpl. apply fmon_le_compat. reflexivity.
  apply IHn.
Qed.

Lemma FChainCore_S: forall (A B : cpoType) (n : natO),
    FChainCore A B n <= FChainCore A B (n.+1)%N.
Proof.
  intros θ c n.
  induction n.
  simpl. intro d. apply leastP.
  intros [d η].
  simpl. apply fmon_le_compat. reflexivity.
  apply FChainCore_S_unfold.
Qed.

Lemma FChain_S : forall (A B : cpoType) (n : natO),
    (FChain A B n) <= (FChain A B (n.+1)%N).
Proof.
  intros A B n.
  induction n.
  intros d η. apply leastP.
  intros d η. simpl.
  apply fmon_le_compat. reflexivity.
  apply pair_le_compat. specialize (IHn d η).
  simpl in IHn. apply IHn. auto.
Qed.

Lemma FChainCore_mon (A B : cpoType) (d : (B -=> A _BOT -=> A _BOT) * B) :
  monotonic (fun (n : natO) => FChainCore A B n d).
Proof.
  intros A B d n n' H.
  assert (forall x y, (x <= y)%coq_nat -> FChainCore A B x <= FChainCore A B y).
  intros x y H0.
  induction H0. auto.
  eapply Ole_trans.
  apply IHle. apply FChainCore_S.
  apply H0.
  assert ((n <= n')%coq_nat <-> n <= n').
  apply rwP. apply leP.
  inversion H1. apply H3.
  apply H.
Qed.

Lemma FChain_mon (A B : cpoType) (d : A _BOT * B -=> A _BOT) :
  monotonic (fun (n : natO) => FChain A B n d).
Proof.
  intros A B d n n' H.
  assert (forall m m', (m <= m')%coq_nat -> FChainCore A B m <= FChainCore A B m').
  - Case "Assert".
    intros m m' H0.
    induction H0.
    -- SCase "m = m'". auto.
    -- SCase "m <= m' ⇒ m <= m'+1".
       eapply Ole_trans.
       apply IHle. apply FChainCore_S.
  simpl.
  apply comp_le_ord_compat.
  apply H0.
  assert ((n <= n')%coq_nat <-> n <= n') by (apply rwP; apply leP).
  apply (snd H1). apply H.
  apply Ole_refl.
Qed.

Definition FC (A B : cpoType) (d : A _BOT * B -=> A _BOT)
  := Eval hnf in mk_fmono (FChain_mon d).

Lemma FC_simpl : forall (A B : cpoType) (d : A _BOT * B -=> A _BOT) (n : natO),
    FC d n =-= FChain A B n d.
Proof. auto. Qed.

Lemma FC_zero : forall (A B : cpoType) (d : A _BOT * B -=> A _BOT),
    FC d 0%N =-= const _ PBot.
Proof.
  intros A B d. apply fmon_eq_intro.
  intro η. by simpl.
Qed.

Lemma FC_unfold : forall (A B : cpoType) (d : A _BOT * B -=> A _BOT) (n : natO),
    FC d (n.+1)%N =-= ev << <| CURRY (SwapArgs d) , FC d n |>.
Proof.
  intros A B d n. simpl.
  apply fmon_eq_intro.
  intro η. by simpl.
Qed.

Lemma FC_lub : forall (A B : cpoType) (d : A _BOT * B -=> A _BOT),
    lub (FC d) =-= FixF d.
Proof.
  intros A B d.
  apply fmon_eq_intro. intro η.
  apply lub_eq_compat. simpl.
  apply fmon_eq_intro. intro n.
  induction n.
  simpl. apply tset_refl.
  simpl.
  apply fmon_eq_compat. reflexivity.
  apply pair_eq_compat.
  apply pair_eq_compat. auto.
  simpl in IHn. apply IHn. auto.
Qed.

Lemma FC_Prop : forall (A B : cpoType) (b : B) (d : A _BOT * B -=> A _BOT)
                  (j : natO),
    FC d (j.+1)%N b =-= d (FC d j b, b).
Proof.
  intros A B b d j.
    by simpl.
Qed.
