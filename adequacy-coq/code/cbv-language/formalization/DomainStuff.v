Add LoadPath "../domain-theory".

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

Require Import Utils.
Require Import Program.
Require Import PredomRec.
Require Import Domains.
Require Import domoprs.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.

Definition KR := kleisli (eta << Roll).
Definition KUR := kleisli (eta << Unroll).

Lemma discrete_eq : forall (A : Type) (d d' : discrete_cpoType A),
    d =-= d' -> d = d'.
Proof.
  intros A d d' H.
  inversion H. inversion H0. auto.
Qed.

Lemma EpsStable (D : cpoType) a b : (a =-= b ) ->
                                    (@tset_eq (D _BOT) (Eps a) (Eps b)). 
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

Definition IfBCore (A : Type) (a a' : A) (b : bool_cpoType) : A :=
  match b with
  | true   => a
  | false  => a'
  end
.

Lemma IfBCore_mon
      (A B : ordType) :
      monotonic (fun p : (A -=> B) * (A -=> B) * A * discrete_ordType bool =>
                   (IfBCore (fst (fst (fst p))) (snd (fst (fst p))) (snd p))
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

Definition IfBCoreM (A B : ordType) :
  ((A -=> B) * (A -=> B) * A * discrete_ordType bool) =-> B
  := Eval hnf in mk_fmono (@IfBCore_mon A B).

Lemma IfBCore_mon2
      (A B : cpoType) :
      monotonic (fun p : (A -=> B) * (A -=> B) * discrete_cpoType bool =>
                   IfBCore (fst (fst p)) (snd (fst p)) (snd p)
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

Definition IfBCoreM2 (A B : cpoType)
  := Eval hnf in mk_fmono (@IfBCore_mon2 A B).

Lemma IfBCore_cont2 (A B : cpoType) :
  continuous (@IfBCoreM2 A B).
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

Definition IfB (A B : cpoType)
  := Eval hnf in mk_fcont (@IfBCore_cont2 A B).

Definition IfZCore (A : Type) (a a' : A) (n : nat_cpoType) : A :=
  match n with
  | O   => a
  | S _ => a'
  end
.

Lemma IfZCore_mon
      (A B : ordType) :
      monotonic (fun p : (A -=> B) * (A -=> B) * A * discrete_ordType nat =>
                   (IfZCore (fst (fst (fst p))) (snd (fst (fst p))) (snd p))
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

Definition IfZCoreM (A B : ordType) :
  ((A -=> B) * (A -=> B) * A * discrete_ordType nat) =-> B
  := Eval hnf in mk_fmono (@IfZCore_mon A B).

Lemma IfZCore_mon2
      (A B : cpoType) :
      monotonic (fun p : (A -=> B) * (A -=> B) * discrete_cpoType nat =>
                   IfZCore (fst (fst p)) (snd (fst p)) (snd p)
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

Definition IfZCoreM2 (A B : cpoType)
  := Eval hnf in mk_fmono (@IfZCore_mon2 A B).

Lemma IfZCore_cont2 (A B : cpoType) :
  continuous (@IfZCoreM2 A B).
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

Definition IfZ (A B : cpoType)
  := Eval hnf in mk_fcont (@IfZCore_cont2 A B).

(* Unary OP *)
Lemma SimpleU_mon (A :Type) (B:ordType) (op : A -> B:Type) :
  monotonic (fun a:discrete_ordType A => op a).
Proof.
  move => A B op. intros x y H.
  have e:x = y by []. by rewrite e.
Qed.

Definition SimpleUOpm (A : Type) (B : ordType) (op : A -> B) :
  discrete_ordType A =-> B :=
  Eval hnf in mk_fmono (SimpleU_mon op).

Lemma SimpleU_cont (A : Type) (B : cpoType) (op : A -> B) :
  @continuous (discrete_cpoType A) B (SimpleUOpm op).
Proof.
  move => A B op.
  move => c. simpl. apply: (Ole_trans _ (le_lub _ 0)). simpl.
    by [].
Qed.

Definition SimpleUOp (A : Type) (B : cpoType) (op : A -> B) :
  discrete_cpoType A =-> B :=
  Eval hnf in mk_fcont (SimpleU_cont op).

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

Definition if3 (n : nat) : bool_cpoType _BOT :=
  match n with
  | 0   => eta false
  | S 0 => eta true
  | S _ => PBot
  end.

Definition IF3 : nat_cpoType =-> bool_cpoType _BOT := SimpleUOp if3.

Definition N_to_B : nat_cpoType =-> bool_cpoType _BOT := IF3.

Definition B_to_N : bool_cpoType =-> nat_cpoType
  := Fcont_app ((CURRY (@IfB one_cpoType nat_cpoType))
                 ((const one_cpoType 1), (const one_cpoType 0))) ().

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

Lemma pairInj_eq : forall (A B : cpoType) (a c : A)  (b d : B),
    PAIR _ a b =-= (c, d) -> a =-= c /\ b =-= d.
Proof.
  intros A B a c b d H; simpl in *.
  inversion H as [[? ?] [? ?]]; simpl in *.
  split; split; auto.
Qed.

Lemma Smash_ValVal : forall (A B : cpoType) (a : A) (b : B),
    Smash _ _ (Val a) (Val b) =-= Val (a, b).
Proof.
  intros A B a b.
  unfold Smash, Operator2. unlock. simpl.
  rewrite -> kleisliVal. simpl. rewrite -> kleisliVal.
  simpl. rewrite -> kleisliVal. by simpl.
Qed.

Lemma pairl_mon (O0 O1 : ordType) (y:O1) : monotonic (fun (x:O0) => (x,y)).
  move => O0 O1 x y y' l. by rewrite -> l.
Qed.

Definition Pairl (O0 O1 : ordType) (y:O1) : O0 =-> (O0 * O1) :=
  Eval hnf in mk_fmono (pairl_mon y).

Lemma Pairl_cont (D0 D1 : cpoType) (y:D1) : continuous (@Pairl D0 D1 y).
  move => D0 D1 y c. simpl. split.
  - simpl. by apply lub_le_compat => i.
  - simpl. by apply: (Ole_trans _ (le_lub (pi2 << (Pairl D0 y << c)) O)). 
Qed.

Definition PAIRL (D0 D1 : cpoType) (y:D1) : D0 =-> D0 * D1 :=
  Eval hnf in mk_fcont (Pairl_cont y).

Lemma PAIR_eq : forall (D0 D1 : cpoType) (x : D0),
    SWAP << (@PAIR D0 D1) x =-= @PAIRL D1 D0 x.
Proof.
  intros D0 D1 x. split; intros y; auto.
Qed.

Lemma SmashInv (C D : cpoType) : forall a b c d, Smash C D a b =-= Val (c , d) ->
                                 Val c =-= a /\ Val d =-= b.
Proof.
  intros C D a b c d H.
  unfold Smash in H.
  apply Operator2Val in H.
  destruct H as [c' [d' [eqa [eqb eqp]]]].
   apply DLleVal_eq2 in eqp.
   apply pairInj_eq  in eqp as [eqc eqd].
   split.
  rewrite eqa. symmetry. by apply Val_eq_compat.
  rewrite eqb. symmetry. by apply Val_eq_compat.
Qed.
