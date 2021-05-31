Add LoadPath "../domain-theory".

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

Require Import Utils.
Require Import PredomAll.
Require Import PredomRec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition prod_morph (A B C D : cpoType)
           (fg : (A =-> B) * (C =-> D)) :=
  prod_fun ((fst fg) << pi1) ((snd fg) << pi2). 

Definition PRODm_morph (A B C D : cpoType):
  monotonic (fun (fg :  (A =-> B) * (C =-> D)) => (@prod_morph A B C D fg)).
Proof.
  intros A B C D. intros (f, g) (f',g') l.
  intros (a,c). simpl. destruct l. rewrite -> H, H0. auto.
Qed.

Definition prodm_morph (A B C D : cpoType) :=
  Eval hnf in mk_fmono (@PRODm_morph A B C D).

Definition PRODc_morph (A B C D : cpoType) :
  continuous (@prodm_morph A B C D ).
Proof.
  intros A B C D. intros fgi. intros (a,c). simpl.
  rewrite -> pair_lub. auto.
Qed.

Definition pprodc_morph (A B C D : cpoType) :=
  Eval hnf in mk_fcont (@PRODc_morph A B C D).

Definition prodc_morph (A B C D : cpoType) := CURRY (pprodc_morph A B C D).
Arguments prodc_morph [A B C D].

Lemma lub_prod_fun : forall (D1 D2 D3 D4 D5 : cpoType) (d2 : D2) (d4 : D4)
                       (f : cpoCatType D1 (D2 -=> D3))
                       (g : cpoCatType D1 (D4 -=> D5))
                       (h : ordCatType natO D1),
    (f (lub h) >< g (lub h)) (d2,d4) =-= lub
                             (<| (mk_fmono (fcont_lub_mono (ocomp f h))) d2,
                              (mk_fmono (fcont_lub_mono (ocomp g h))) d4 |>).
Proof.
  intros D1 D2 D3 D4 D5 d2 d4 f g h.
  do 2 rewrite -> lub_comp_eq. simpl.
  rewrite -> pair_lub. by simpl.
Qed.

Lemma able : forall (A B C D : cpoType)
               (fa : A =-> C _BOT) (fb : B =-> D _BOT) (a : A),
    (uncurry (Smash C D) << prod_morph (fa, fb)) << PAIR B a
                                                 =-=
                                                 (Smash C D) (fa a) << fb.
Proof.
  intros A B C D fa fb a.
  split; intro b; by simpl.
Qed.  
  
Lemma miguel : forall (A B C : cpoType)
                 (f : B =-> C _BOT) (a : A _BOT) b,
    (((Smash A C) a) << kleisli f) b =-= (kleisli ((Smash A C) a << f)) b.
Proof.
  intros A B C f a b.
  repeat rewrite kleisli_simpl. 
  rewrite  kleislit_comp.
  simpl. by rewrite kleisli_simpl.
  intros x xx0 H.
  unfold Smash, Operator2 in H; unlock in H; simpl in H.
  apply kleisliValVal in H. destruct H as [fc [? ?]].
  apply kleisliValVal in H. destruct H as [a' [? ?]].
  apply kleisliValVal in H0. destruct H0 as [c' [? ?]].
  simpl in *.
  exists c'. auto.
Qed.

Lemma Smash_Eps_l :
  forall (A B : cpoType) (d : A _BOT) (d' : B _BOT),
    (Smash A B) (Eps d) d' = Eps ((Smash A B) d d').
Proof.
  intros A B d d'.
  unfold Smash. unfold Operator2. unlock. simpl.
  do 2 rewrite kleisli_simpl. do 2 rewrite kleisli_Eps.
  by do 2 rewrite <- kleisli_simpl.
Qed.

Lemma Smash_Val : forall (A B : cpoType) (a : A) (b : B _BOT),
    (Smash A B) (Val a) b = (kleisli (eta << PAIR B a)) b.
Proof.
  intros A B a b.
  unfold Smash. unfold Operator2. unlock. simpl.
  do 2 rewrite kleisli_simpl. repeat rewrite kleisli_Val. by simpl.
Qed.

Lemma Smash_prop_r : forall (B C E F : cpoType)
                       (fa : B =-> C _BOT) (ga : B _BOT)
                       (fb : E =-> F _BOT) (gb : E _BOT),
    Smash _ _ ((kleislit fa) ga) ((kleislit fb) gb)
    <=
    kleislit (uncurry (Smash _ _ ) << prod_morph (fa, fb))
             (Smash _ _ ga gb).
Proof.
  cofix Smash_prop_r.
  intros B C E F fa ga fb gb.
  destruct ga. rewrite Smash_Eps_l.
  repeat rewrite -> kleisli_Eps.
  rewrite Smash_Eps_l. apply DLleEps.
  apply Smash_prop_r.
  rewrite -> Smash_Val.
  rewrite <- kleisli_simpl.
  rewrite -> kleisliVal.
  rewrite -> kleisli_simpl.
  repeat rewrite <- kleisli_simpl.
  assert ((kleisli (uncurry (Smash C F) << prod_morph (fa, fb)))
            ((kleisli (eta << PAIR E s)) gb)
            =-=
            (kleisli (uncurry (Smash C F) << prod_morph (fa, fb))
                     <<
                     (kleisli (eta << PAIR E s))) gb
         ) by auto.
  rewrite -> H; clear H.
  rewrite <- kleisli_comp2.
  assert (((Smash C F) (fa s)) ((kleisli fb) gb)
                               =-=
                               ((Smash C F) (fa s) << (kleisli fb)) gb
         ) by auto. rewrite -> H; clear H.
  rewrite -> miguel.
  rewrite -> able. auto.
Qed.

Lemma Smash_prop_l : forall (B C E F : cpoType)
                       (fa : B =-> C _BOT) (ga : B _BOT)
                       (fb : E =-> F _BOT) (gb : E _BOT),
    kleislit (uncurry (Smash _ _ ) << prod_morph (fa, fb))
             (Smash _ _ ga gb)
    <=
    Smash _ _ ((kleislit fa) ga) ((kleislit fb) gb).
Proof.
  cofix Smash_prop_l.
  intros B C E F fa ga fb gb.
  destruct ga. rewrite Smash_Eps_l.
  repeat rewrite -> kleisli_Eps.
  rewrite Smash_Eps_l. apply DLleEps.
  apply Smash_prop_l.
  rewrite -> Smash_Val.
  repeat rewrite <- kleisli_simpl.
  rewrite -> kleisliVal.
  rewrite -> kleisli_simpl.
  repeat rewrite <- kleisli_simpl.
  assert ((kleisli (uncurry (Smash C F) << prod_morph (fa, fb)))
            ((kleisli (eta << PAIR E s)) gb)
            =-=
            (kleisli (uncurry (Smash C F) << prod_morph (fa, fb))
                     <<
                     (kleisli (eta << PAIR E s))) gb
         ) by auto.
  rewrite -> H; clear H.
  rewrite <- kleisli_comp2.
  assert (((Smash C F) (fa s)) ((kleisli fb) gb)
                               =-=
                               ((Smash C F) (fa s) << (kleisli fb)) gb
         ) by auto. rewrite -> H; clear H.
  rewrite -> miguel.
  rewrite -> able. auto.
Qed.
  
Lemma Smash_prop : forall (B C E F : cpoType)
                     (fa : B =-> C _BOT) (ga : B _BOT)
                     (fb : E =-> F _BOT) (gb : E _BOT),
    Smash _ _ ((kleisli fa) ga) ((kleisli fb) gb)
          =-=
          kleisli (uncurry (Smash _ _ ) << prod_morph (fa, fb))
          (Smash _ _ ga gb).
Proof.
  intros B C E F fa ga fb gb.
  repeat rewrite -> kleisli_simpl.
  split; simpl.
  apply Smash_prop_r.
  apply Smash_prop_l.
Qed.

Lemma Smash_ValVal : forall (A B : cpoType) (a : A) (b : B),
    Smash _ _ (Val a) (Val b) =-= Val (a, b).
Proof.
  intros A B a b.
  unfold Smash, Operator2. unlock. simpl.
  rewrite -> kleisliVal. simpl. rewrite -> kleisliVal.
  simpl. rewrite -> kleisliVal. by simpl.
Qed.
