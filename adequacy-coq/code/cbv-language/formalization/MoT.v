(*begin hide*)
Require Import Utils.
Require Import Program.

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

Add LoadPath "../domain-theory".
Add LoadPath "../extended-cbn".

Require Import Lang.
Require Import Types.
Require Import DomainStuff.

Require Import OperSem.
Require Import ExSem.
Require Import InSem.

Require Import Rel.
Require Import Sets.

Require Import domoprs.
Require Import PredomAll.
Require Import Domains.

Include RD.

Require Import StrictExt.
Require Import EmbProjPair.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

(** *)
(*** Chapter 4: MEANING OF TYPES
***)
(** *)

(** *Definition 48: Logical relations between intrinsic and extrinsic semantics
 *)

Fixpoint _delta (θ : LType) : SemType θ -> DInf -> Prop :=
  match θ as θ return SemType θ -> DInf -> Prop with
  | bool̂      => fun b v => (VInfToNat << Unroll) v =-= eta (B_to_N b)
  | nat̂       => fun n v => (VInfToNat << Unroll) v =-= eta n
  | θ' ⇥ θ'' => let _rho (θ1 : LType) : SemType θ1 _BOT -> DInf _BOT -> Prop
                   := @SE (SemType θ1) DInf (@_delta θ1)
                 in fun f fv => exists g, fv =-= Roll (↑f g) /\
                                forall (x : SemType θ') (y : DInf),
                                  @_delta θ' x y ->
                                  @_rho θ'' (f x) (g y)
  | θ' ⨱ θ''  => fun p pv => exists pv1 pv2, pv =-= Roll (inPair (pv1,pv2)) /\
                                    @_delta θ'  (fst p) pv1 /\
                                    @_delta θ'' (snd p) pv2
  end.

Definition _rho (θ : LType) := @SE (SemType θ) DInf (@_delta θ).

(** *Notation *)
Notation "'δ[' θ ']'"  := (@_delta θ) (at level 1, no associativity).
Notation "'ρ[' θ ']'"  := (@_rho θ) (at level 1, no associativity).

(* Las relaciones son cerradas respecto de la igualdad *)
Lemma deltaBoolCompat : RelStable δ[bool̂].
Proof.
  unfold RelStable.
  intros a a' b b' eqa eqb rel .
  simpl in * .
  rewrite <- eqb.
  rewrite <- eqa. auto.
Qed.

Lemma deltaNatCompat : RelStable δ[nat̂].
Proof.
  unfold RelStable.
  intros a a' b b' eqa eqb rel.
  simpl in *.
  eapply tset_trans.
  apply fmon_eq_compat. reflexivity.
  rewrite <- eqb. reflexivity.
  symmetry.
  eapply tset_trans.
  apply Val_eq_compat with (D:=nat_cpoType).
  rewrite <- eqa. reflexivity.
  auto.
Qed.

Lemma deltaPairCompat : forall (θ1 θ2 : LType),
    RelStable δ[θ1] ->
    RelStable δ[θ2] ->
    RelStable δ[θ1 ⨱ θ2].
Proof.
  intros θ1 θ2 IH1 IH2.
  intros a a' b b' eqa eqb rel.
  simpl in *.
  destruct rel as [pv1 [pv2 [eq [? ?]]]].
  exists pv1, pv2. split. rewrite <- eq. auto.
  split.
  eapply IH1 with (a:=fst a). split; apply eqa. reflexivity. auto.
  eapply IH2 with (a:=snd a). split; apply eqa. reflexivity. auto.  
Qed.

Lemma rhoBoolCompat : RelStable ρ[bool̂].
Proof.
  intros a a' b b' eqa eqb rel  .
  apply (SEStable deltaBoolCompat  eqa eqb rel).
Qed.

Lemma rhoNatCompat : RelStable ρ[nat̂].
Proof.
  intros a a' b b' eqa eqb rel  .
  apply (SEStable deltaNatCompat  eqa eqb rel).
Qed.

Lemma deltaArrow (θ1 θ2 : LType) : RelStable δ[θ2] -> RelStable δ[θ1 ⇥ θ2].
Proof.
  intros θ1 θ2  rr2 f f' a a' eqf eqa rel.
  simpl in *. destruct rel as [g [? ?]]. exists g.
  split. rewrite <- eqa. assumption.
  intros x y H1.
  eapply (SEStable rr2).
  3 : { apply (H0 _ _ H1). }
  by rewrite eqf. reflexivity.
Qed.

Lemma delta_rho_compat (θ : LType): (RelStable δ[θ]) /\ (RelStable ρ[θ]).
Proof.
  intro θ.
  induction θ.
  - split.
    apply deltaBoolCompat. apply rhoBoolCompat.
  - split.
    apply deltaNatCompat. apply rhoNatCompat.
  -  destruct IHθ2 as [stable_v stable_e].
     split. apply deltaArrow. assumption.
     intros c c' d d' eqc eqd rel. 
     apply (SEStable (deltaArrow stable_v) eqc eqd rel).
  - split.
    apply deltaPairCompat. apply IHθ1. apply IHθ2.
    apply SEStable. apply deltaPairCompat. apply IHθ1. apply IHθ2.
Qed.

Lemma deltaNatOpt
      (f : nat_cpoType =-> nat_cpoType _BOT)
      (g : DInf =-> DInf _BOT) :
  (forall n v, δ[nat̂] n v ->  ρ[nat̂] (f n) (g v)) -> forall d x,
    ρ[nat̂] d x -> ρ[nat̂] (kleislit f d) (kleislit g x).
Proof.
  intros f g hip.
  cofix deltaNatOpt. intros d x rel. 
  inversion rel.
  rewrite kleisli_Eps. 
  rewrite kleisli_Eps. 
  apply SB.
  eapply deltaNatOpt.
  apply H.
  assert (kleislit f d =-= f d0).
  assert (d =-= Val d0).
  rewrite <- H.
  symmetry. apply pred_nth_eq.
  apply tset_trans with (y:= kleislit f (Val d0)).
  apply monotonic_stable.
  apply kleislit_mono.
  apply H4.
  by rewrite kleisli_Val.
  assert (kleislit g x =-= g d').
  assert (x =-= Val d').
  rewrite <- H0.
  symmetry. apply pred_nth_eq.
  apply tset_trans with (y:= kleislit g (Val d')).
  apply monotonic_stable.
  apply kleislit_mono.
  apply H5.
  by rewrite kleisli_Val.
  eapply rhoNatCompat.
  apply (tset_sym H4).
  apply (tset_sym H5).
  by apply hip.
Qed.

Lemma deltaNatOp
      (f : nat_cpoType =-> nat_cpoType _BOT)
      (g : DInf =-> DInf _BOT) :
  (forall n v, δ[nat̂] n v ->  ρ[nat̂] (f n) (g v)) -> forall d x,
  ρ[nat̂] d x -> ρ[nat̂] (kleisli f d) (kleisli g x).
Proof.
  intros f g hip d x rel.
  eapply rhoNatCompat.
  rewrite kleisli_simpl. reflexivity.
  rewrite kleisli_simpl. reflexivity.
  by apply (deltaNatOpt hip).
Qed.

Lemma OpSimplR (A B C : cpoType) (f : A * B =-> C _BOT) : 
  forall (d : A _BOT) (d' : B _BOT),
    DLle (kleisli (ev << <| KLEISLI , const _ d' |>)
                  (kleisli (eta << exp_fun f) d)
         )
         (kleisli f ((kleisli ((uncurry KLEISLI << SWAP)
                                 <<
                                 PAIR _ d'))
                       ((kleisli (eta << exp_fun eta)) d)
                    )
         ).
Proof.
  intros A B C f. cofix OpSimplR. intros d d'.
  destruct d as [e | n].
  repeat (rewrite kleisli_simpl). 
  repeat (rewrite kleisli_Eps).
  repeat (rewrite <- kleisli_simpl). 
  apply (@DLleEps C).
  apply (OpSimplR e d').
  destruct d' as [e' | m].
  repeat (rewrite kleisli_simpl). 
  repeat (rewrite kleisli_Eps).
  repeat (rewrite <- kleisli_simpl). 
  repeat (rewrite kleisliVal).
  simpl.
  rewrite <- comp_simpl.
  rewrite kleisli_comp.
  repeat (rewrite kleisli_simpl; rewrite kleisli_Eps).
  repeat (rewrite <- kleisli_simpl).
  apply DLleEps.
  rewrite comp_assoc.
  rewrite kleisli_eta_com.
  apply Ole_refl.
  repeat (rewrite kleisliVal).
  simpl.
  repeat (rewrite kleisliVal).
  apply Ole_refl.
Qed.

Lemma OpSimplL (A B C : cpoType) (f : A * B =-> C _BOT) : 
  forall (d : A _BOT) (d' : B _BOT),
    DLle (kleisli f ((kleisli ((uncurry KLEISLI << SWAP)
                                 <<
                                 PAIR _ d')
                     ) ((kleisli (eta << exp_fun eta)) d)
                    )
         )
         (kleisli (ev << <| KLEISLI , const _ d' |>)
                  (kleisli (eta << exp_fun f) d)
         ).
Proof.
  intros A B C f. cofix OpSimplL. intros d d'.
  destruct d as [e | n].
  repeat (rewrite kleisli_simpl). 
  repeat (rewrite kleisli_Eps).
  repeat (rewrite <- kleisli_simpl). 
  apply (@DLleEps C).
  apply (OpSimplL e d').
  destruct d' as [e' | m].
  repeat (rewrite kleisli_simpl). 
  repeat (rewrite kleisli_Eps).
  repeat (rewrite <- kleisli_simpl). 
  repeat (rewrite kleisliVal).
  simpl.
  rewrite <- comp_simpl.
  rewrite kleisli_comp.
  repeat (rewrite kleisli_simpl; rewrite kleisli_Eps).
  repeat (rewrite <- kleisli_simpl).
  apply DLleEps.
  rewrite comp_assoc.
  rewrite kleisli_eta_com.
  apply Ole_refl.
  repeat (rewrite kleisliVal).
  simpl.
  repeat (rewrite kleisliVal).
  apply Ole_refl.
Qed.

Lemma genbinopsimpl (A B : Type) (C : cpoType)
      (f : A -> B -> C) :
  forall d d',
    GenBinOpTy f d d' ()
      =-= 
    (kleisli (ev << <| KLEISLI, const _ (d' ()) |>))
      (kleisli (eta << exp_fun (eta << SimpleBOp f)) (d ())).
Proof.
  intros f d d'.
  simpl.
  unfold Smash; unfold Operator2; unlock; simpl.
  split. apply OpSimplL. apply OpSimplR.
Qed.

Definition injnToDInf : nat_cpoType -=> DInf := Roll << in1 << in1.
Definition DInfToNat : DInf _BOT -=> nat_cpoType _BOT :=
  kleisli (toI nat̂ << Unroll).

Definition GenBinOpIn
           (A B : Type)
           (C : cpoType)
           (f : A -> B -> C)
           (d : discrete_cpoType A _BOT)
           (d' : discrete_cpoType B _BOT)
  : discrete_cpoType C _BOT :=
  (((kleisli (ev << <| KLEISLI, const _ d'  |>))
      ((kleisli (eta << exp_fun
                     (eta << @SimpleBOp _ _ _  f))) d))).

Lemma GenBinOpSimpl (A B : Type) (C : cpoType) (f : A -> B -> C) d d' :
  GenBinOpTy f d d' () =-= GenBinOpIn f (d ()) (d' ()).
Proof.
  intros A B C f d d'.
  unfold GenBinOpIn.
    by rewrite genbinopsimpl.
Qed.

Lemma DInfToNat_bot (g : DInf -=> DInf _BOT) :
  VInfToNat (↑f g) =-= PBot.
Proof.
  intro g. unfold DInfToNat.
  by do 2 setoid_rewrite SUM_fun_simplx.
Qed.

Lemma DInfToNat_bot' (p : DInf * DInf) :
  VInfToNat (inPair p) =-= PBot.
Proof.
  intro p. unfold DInfToNat.
  by rewrite SUM_fun_simplx.
Qed.

Lemma simpE (f : nat -> nat -> nat) (x x' : VInf _BOT) :
   DLle
     ((kleisli ((eta << inNat) << SimpleBOp f))
        (kleisli
           ((uncurry KLEISLI << SWAP)
              <<
              PAIR (nat_cpoType -=> (nat_cpoType * nat_cpoType) _BOT)
              (kleisli VInfToNat x'))
           (kleisli (eta << exp_fun eta) (kleisli VInfToNat x))
        )
     )
     ((kleisli ((kleisli (eta << in1 << in1) << ev)
                  << <| KLEISLI, const (nat_cpoType -=> nat_cpoType _BOT)
                                       (kleisli VInfToNat x') |>)
      )
        ((kleisli (eta << exp_fun (eta << SimpleBOp f))) (kleisli VInfToNat x))
     ).
Proof.
  intros f. cofix simpE. intros x x'.
  destruct x as [x | v].
  repeat (rewrite kleisli_simpl). 
  repeat (rewrite kleisli_Eps).
  repeat (rewrite <- kleisli_simpl). 
  apply DLleEps.
  apply (simpE x x').
  destruct v as [[n | g] | p].
  - Case "nat".
    repeat (rewrite kleisliVal).
    do 2 rewrite SUM_fun_simplx.
    repeat rewrite <- comp_simpl.
    rewrite <- kleisli_comp2.
    unfold injnToDInf. simpl.
    repeat rewrite kleisliVal.
    simpl. rewrite <- (comp_assoc (PAIR _ _) (SimpleBOp f) eta).
    repeat rewrite <- comp_simpl. do 2 rewrite <- kleisli_comp2. simpl.
    unfold inNat. repeat rewrite -> comp_assoc.
    apply DLle_refl.
  - Case " ⇥ ".
    repeat rewrite -> kleisliVal.
    do 2 rewrite SUM_fun_simplx.
    repeat (rewrite kleisli_bot).
    apply DLle_refl.
  - Case "⨱".
    repeat rewrite -> kleisliVal.
    rewrite SUM_fun_simplx.
    repeat (rewrite kleisli_bot).
    apply DLle_refl.
Qed.

Lemma simpE' f x x' : 
   DLle
     ((kleisli ((kleisli (eta << in1 (B:=DInf * DInf) <<
                              in1 (B:=DInf -=> DInf _BOT)) << ev) << <| KLEISLI, const (nat_cpoType -=> nat_cpoType _BOT) (kleisli VInfToNat x') |>))
        ((kleisli (eta << exp_fun (eta << SimpleBOp f))) (kleisli VInfToNat x)))
     ((kleisli ((eta << inNat) << SimpleBOp f))
        ((kleisli
            ((uncurry KLEISLI << SWAP) << PAIR (discrete_cpoType nat -=> (discrete_cpoType nat * discrete_cpoType nat) _BOT) (kleisli VInfToNat x')))
           ((kleisli (eta << exp_fun eta)) (kleisli VInfToNat x))))
.
Proof.
  intros f. cofix simpE'. intros x x'.
  destruct x as [x | v].
  repeat (rewrite kleisli_simpl). 
  repeat (rewrite kleisli_Eps).
  repeat (rewrite <- kleisli_simpl). 
  apply DLleEps.
  apply (simpE' x x').
  destruct v as [[n | g] | p].
  - Case "nat".
    repeat (rewrite kleisliVal).
    do 2 rewrite SUM_fun_simplx.
    repeat rewrite <- comp_simpl.
    rewrite <- kleisli_comp2.
    unfold injnToDInf. simpl.
    repeat rewrite kleisliVal.
    simpl. rewrite <- (comp_assoc (PAIR _ _) (SimpleBOp f) eta).
    repeat rewrite <- comp_simpl. do 2 rewrite <- kleisli_comp2. simpl.
    unfold inNat. repeat rewrite -> comp_assoc.
    apply DLle_refl.
  - Case " ⇥ ".
    repeat rewrite -> kleisliVal.
    do 2 rewrite SUM_fun_simplx.
    repeat (rewrite kleisli_bot).
    apply DLle_refl.
  - Case "⨱".
    repeat rewrite -> kleisliVal.
    rewrite SUM_fun_simplx.
    repeat (rewrite kleisli_bot).
    apply DLle_refl.
Qed.

Lemma natopsimplE f : 
  forall d d',
    (@GenNatOp O f d d' ())
      =-= 
      (kleisli (kleisli (eta << in1 << in1) << ev <<
                        <| KLEISLI , const _  (kleisli VInfToNat (d' ())) |>)
               ((kleisli (eta << exp_fun (eta
                 <<
                 @SimpleBOp nat_cpoType nat_cpoType _  f)))
                  (kleisli VInfToNat (d ())))).
Proof.
  intros f d d'.
  simpl.
  unfold Smash; unfold Operator2; unlock; simpl.
  split; simpl.
  apply (simpE f (d ()) (d' ())).
  apply (simpE' f (d ()) (d' ())).
Qed.

Lemma OrdsimpE (f : nat -> nat -> bool) (x x' : VInf _BOT) :
   DLle
     ((kleisli ((eta << inNat << B_to_N) << SimpleBOp f))
        (kleisli
           ((uncurry KLEISLI << SWAP)
              <<
              PAIR _
              (kleisli VInfToNat x'))
           (kleisli (eta << exp_fun eta) (kleisli VInfToNat x))
        )
     )
     ((kleisli ((kleisli (eta << in1 << in1 << B_to_N) << ev)
                  << <| KLEISLI, const _
                                       (kleisli VInfToNat x') |>)
      )
        ((kleisli (eta << exp_fun (eta << SimpleBOp f))) (kleisli VInfToNat x))
     ).
Proof.
  intros f. cofix OrdsimpE. intros x x'.
  destruct x as [x | v].
  repeat (rewrite kleisli_simpl). 
  repeat (rewrite kleisli_Eps).
  repeat (rewrite <- kleisli_simpl). 
  apply DLleEps.
  apply (OrdsimpE x x').
  destruct v as [[n | g] | p].
  - Case "nat".
    repeat (rewrite kleisliVal).
    do 2 rewrite SUM_fun_simplx.
    repeat rewrite <- comp_simpl.
    rewrite <- kleisli_comp2.
    unfold injnToDInf. simpl.
    repeat rewrite kleisliVal.
    simpl. rewrite <- (comp_assoc (PAIR _ _) (SimpleBOp f) eta).
    repeat rewrite <- comp_simpl. do 2 rewrite <- kleisli_comp2. simpl.
    unfold inNat. repeat rewrite -> comp_assoc.
    apply DLle_refl.
  - Case " ⇥ ".
    repeat rewrite -> kleisliVal.
    do 2 rewrite SUM_fun_simplx.
    repeat (rewrite kleisli_bot).
    apply DLle_refl.
  - Case "⨱".
    repeat rewrite -> kleisliVal.
    rewrite SUM_fun_simplx.
    repeat (rewrite kleisli_bot).
    apply DLle_refl.
Qed.

Lemma OrdsimpE' f x x' : 
   DLle
     ((kleisli ((kleisli (eta << in1 (B:=DInf * DInf) <<
                              in1 (B:=DInf -=> DInf _BOT) << B_to_N) << ev) << <| KLEISLI, const (nat_cpoType -=> bool_cpoType _BOT) (kleisli VInfToNat x') |>))
        ((kleisli (eta << exp_fun (eta << SimpleBOp f))) (kleisli VInfToNat x)))
     ((kleisli ((eta << inNat << B_to_N) << SimpleBOp f))
        ((kleisli
            ((uncurry KLEISLI << SWAP) << PAIR (discrete_cpoType nat -=> (discrete_cpoType nat * discrete_cpoType nat) _BOT) (kleisli VInfToNat x')))
           ((kleisli (eta << exp_fun eta)) (kleisli VInfToNat x))))
.
Proof.
  intros f. cofix OrdsimpE'. intros x x'.
  destruct x as [x | v].
  repeat (rewrite kleisli_simpl). 
  repeat (rewrite kleisli_Eps).
  repeat (rewrite <- kleisli_simpl). 
  apply DLleEps.
  apply (OrdsimpE' x x').
  destruct v as [[n | g] | p].
  - Case "nat".
    repeat (rewrite kleisliVal).
    do 2 rewrite SUM_fun_simplx.
    repeat rewrite <- comp_simpl.
    rewrite <- kleisli_comp2.
    unfold injnToDInf. simpl.
    repeat rewrite kleisliVal.
    simpl. rewrite <- (comp_assoc (PAIR _ _) (SimpleBOp f) eta).
    repeat rewrite <- comp_simpl. do 2 rewrite <- kleisli_comp2. simpl.
    unfold inNat. repeat rewrite -> comp_assoc.
    apply DLle_refl.
  - Case " ⇥ ".
    repeat rewrite -> kleisliVal.
    do 2 rewrite SUM_fun_simplx.
    repeat (rewrite kleisli_bot).
    apply DLle_refl.
  - Case "⨱".
    repeat rewrite -> kleisliVal.
    rewrite SUM_fun_simplx.
    repeat (rewrite kleisli_bot).
    apply DLle_refl.
Qed.

Lemma BoolsimpE (f : bool -> bool -> bool) (x x' : VInf _BOT) :
   DLle
     ((kleisli ((eta << (inNat << B_to_N)) << SimpleBOp f))
        (kleisli
           ((uncurry KLEISLI << SWAP)
              <<
              PAIR _
              (kleisli VInfToBool x'))
           (kleisli (eta << exp_fun eta) (kleisli VInfToBool x))
        )
     )
     ((kleisli ((kleisli (eta << in1 << in1 << B_to_N) << ev)
                  << <| KLEISLI, const _
                                       (kleisli VInfToBool x') |>)
      )
        ((kleisli (eta << exp_fun (eta << SimpleBOp f))) (kleisli VInfToBool x))
     ).
Proof.
  intros f. cofix BoolsimpE. intros x x'.
  destruct x as [x | v].
  repeat (rewrite kleisli_simpl).
  repeat (rewrite kleisli_Eps).
  repeat (rewrite <- kleisli_simpl).
  apply DLleEps.
  apply (BoolsimpE x x').
  destruct v as [[n | g] | p].
  repeat (rewrite kleisliVal).
  do 2 rewrite SUM_fun_simplx.
  repeat rewrite <- comp_simpl.
  rewrite <- kleisli_comp2.
  unfold injnToDInf. simpl.
  destruct n.
  repeat rewrite kleisliVal.
  simpl. rewrite <- (comp_assoc (PAIR _ _) (SimpleBOp f) eta).
  repeat rewrite <- comp_simpl. do 2 rewrite <- kleisli_comp2. simpl.
  unfold inNat. repeat rewrite -> comp_assoc.
  apply DLle_refl.
  destruct n.
    repeat rewrite kleisliVal.
  simpl. rewrite <- (comp_assoc (PAIR _ _) (SimpleBOp f) eta).
  repeat rewrite <- comp_simpl. do 2 rewrite <- kleisli_comp2. simpl.
  unfold inNat. repeat rewrite -> comp_assoc.
  apply DLle_refl.
  simpl. repeat rewrite kleisli_bot. apply DLle_refl.
  repeat (rewrite kleisliVal).
  do 2 rewrite SUM_fun_simplx.
  repeat (rewrite kleisliVal).
  simpl.
  repeat (rewrite kleisli_bot).
  apply DLle_refl.
  repeat rewrite -> kleisliVal.
  rewrite SUM_fun_simplx.
  repeat (rewrite kleisli_bot).
  apply DLle_refl.
Qed.

Lemma BoolsimpE' f x x' :
   DLle
     ((kleisli ((kleisli (eta << in1 (B:=DInf * DInf) <<
                              in1 (B:=DInf -=> DInf _BOT) << B_to_N) << ev) << <| KLEISLI, const (bool_cpoType -=> bool_cpoType _BOT) (kleisli VInfToBool x') |>))
        ((kleisli (eta << exp_fun (eta << SimpleBOp f))) (kleisli VInfToBool x)))
     ((kleisli ((eta << (inNat << B_to_N)) << SimpleBOp f))
        ((kleisli
            ((uncurry KLEISLI << SWAP) << PAIR (discrete_cpoType bool -=> (discrete_cpoType bool * discrete_cpoType bool) _BOT) (kleisli VInfToBool x')))
           ((kleisli (eta << exp_fun eta)) (kleisli VInfToBool x))))
.
Proof.
  intros f. cofix BoolsimpE'. intros x x'.
  destruct x as [x | v].
  repeat (rewrite kleisli_simpl).
  repeat (rewrite kleisli_Eps).
  repeat (rewrite <- kleisli_simpl).
  apply DLleEps.
  apply (BoolsimpE' x x').
  destruct v as [[n | g] | p].
  repeat (rewrite kleisliVal).
  do 2 rewrite SUM_fun_simplx.
  repeat rewrite <- comp_simpl.
  rewrite <- kleisli_comp2.
  unfold injnToDInf. simpl.
  destruct n.
  repeat rewrite kleisliVal.
  simpl. rewrite <- (comp_assoc (PAIR _ _) (SimpleBOp f) eta).
  repeat rewrite <- comp_simpl. do 2 rewrite <- kleisli_comp2. simpl.
  unfold inNat. repeat rewrite -> comp_assoc.
  apply DLle_refl.
  destruct n.
    repeat rewrite kleisliVal.
  simpl. rewrite <- (comp_assoc (PAIR _ _) (SimpleBOp f) eta).
  repeat rewrite <- comp_simpl. do 2 rewrite <- kleisli_comp2. simpl.
  unfold inNat. repeat rewrite -> comp_assoc.
  apply DLle_refl.
  simpl. repeat rewrite kleisli_bot. apply DLle_refl.
  repeat (rewrite kleisliVal).
  do 2 rewrite SUM_fun_simplx.
  repeat (rewrite kleisliVal).
  simpl.
  repeat (rewrite kleisli_bot).
  apply DLle_refl.
  repeat rewrite -> kleisliVal.
  rewrite SUM_fun_simplx.
  repeat (rewrite kleisli_bot).
  apply DLle_refl.
Qed.

Lemma boolopsimplE f :
  forall d d',
    (@GenBoolOp O f d d' ())
      =-=
      (kleisli (kleisli (eta << in1 << in1 << B_to_N) << ev <<
                        <| KLEISLI , const _  (kleisli VInfToBool (d' ())) |>)
               ((kleisli (eta << exp_fun (eta
                 <<
                 @SimpleBOp bool_cpoType bool_cpoType _  f)))
                  (kleisli VInfToBool (d ())))).
Proof.
  intros f d d'.
  simpl.
  unfold Smash; unfold Operator2; unlock; simpl.
  split; simpl.
  apply (BoolsimpE f (d ()) (d' ())).
  apply (BoolsimpE' f (d ()) (d' ())).
Qed.

Lemma ordopsimplE f : 
  forall d d',
    (@GenOrdOp O f d d' ())
      =-= 
      (kleisli (kleisli (eta << in1 << in1 << B_to_N) << ev <<
                        <| KLEISLI , const _  (kleisli VInfToNat (d' ())) |>)
               ((kleisli (eta << exp_fun (eta
                 <<
                 @SimpleBOp nat_cpoType nat_cpoType _  f)))
                  (kleisli VInfToNat (d ())))).
Proof.
  intros f d d'.
  simpl.
  unfold Smash; unfold Operator2; unlock; simpl.
  split; simpl. rewrite -> comp_assoc with (h:=eta).
  apply (OrdsimpE f (d ()) (d' ())).
  rewrite -> comp_assoc with (h:=eta).
  apply (OrdsimpE' f (d ()) (d' ())).
Qed.

Lemma OrdRelBinFun f (n m : nat_cpoType) : forall r,
    r =-= f(n,m) -> ρ[bool̂] r
                    (kleisli (eta << Roll << in1 << in1 << B_to_N) r).
Proof. intros f n m. cofix OrdRelBinFun.
       intros r equ.
       destruct r.
       rewrite kleisli_simpl; rewrite kleisli_Eps.
       rewrite <- kleisli_simpl.
       unfold _rho in OrdRelBinFun.
       rewrite <- eq_Eps in equ.
       specialize (OrdRelBinFun r equ).
       apply (SB OrdRelBinFun).
       eapply rhoBoolCompat.
       reflexivity.
       rewrite kleisliVal.
       by simpl.
       eapply SV with (n := 0) (m:=0).
       apply pred_nth_val.
       apply pred_nth_val.
       unfold _delta. simpl.
       rewrite -> URid. do 2 setoid_rewrite -> SUM_fun_simplx. auto.
Qed.

Lemma BoolRelBinFun f (n m : bool_cpoType) : forall r,
    r =-= f(n,m) -> ρ[bool̂] r (kleisli
                                (eta << Roll << in1 << in1 << B_to_N) r).
Proof. intros f n m. cofix BoolRelBinFun.
       intros r equ.
       destruct r.
       rewrite kleisli_simpl; rewrite kleisli_Eps.
       rewrite <- kleisli_simpl.
       unfold _rho in BoolRelBinFun.
       rewrite <- eq_Eps in equ.
       specialize (BoolRelBinFun r equ).
       apply (SB BoolRelBinFun).
       eapply rhoBoolCompat.
       reflexivity.
       rewrite kleisliVal.
       by simpl.
       eapply SV with (n := 0) (m:=0).
       apply pred_nth_val.
       apply pred_nth_val.
       unfold _delta. simpl.
       rewrite -> URid. do 2 setoid_rewrite -> SUM_fun_simplx. auto.
Qed.

Lemma RollInj x y : Roll x =-= Roll y -> x =-= y.
Proof.
  intros x y H.
  apply tset_trans with (y := Unroll (Roll x)).
  rewrite <- comp_simpl ; by rewrite UR_id.
  setoid_rewrite H.
  rewrite <- comp_simpl ; by rewrite UR_id.
Qed.  

Lemma OrdRelBFun f n :
  forall x y, ρ[nat̂] x y ->
  ρ[bool̂] ((kleisli (f << @PAIR nat_cpoType nat_cpoType n)) x)
   (kleisli (eta << Roll << in1 << in1 << B_to_N)
            ((kleisli (f << PAIR nat_cpoType n))
               ((kleisli (VInfToNat << Unroll)) y))).
Proof.
  intros f n. cofix OrdRelBFun. intros x y rel.
  inversion rel.
  repeat (rewrite kleisli_simpl).
  repeat (rewrite kleisli_Eps).
  apply SB.
  repeat (rewrite <- kleisli_simpl).
  apply (OrdRelBFun _ _ H).
  - Case "nat".
    eapply rhoBoolCompat.
    rewrite <- (@pred_nth_eq _ n0 x).
    rewrite H.
    rewrite kleisliVal. by simpl.
    rewrite <- (@pred_nth_eq _ m y).
    rewrite H0.
    rewrite kleisliVal.
    unfold _delta in H1. 
    rewrite -> H1.
    rewrite kleisliVal. by simpl.
    eapply OrdRelBinFun with (f := f).
    reflexivity.
Qed.

Lemma BoolRelBFun f n : forall x y, ρ[bool̂] x y ->
  ρ[bool̂] ((kleisli (f << @PAIR bool_cpoType bool_cpoType n)) x)
   (kleisli (eta << Roll << in1 << in1 << B_to_N)
            ((kleisli (f << PAIR bool_cpoType n))
               ((kleisli (VInfToBool << Unroll)) y))).
Proof.
  intros f n. cofix BoolRelBFun. intros x y rel.
  inversion rel.
  repeat (rewrite kleisli_simpl).
  repeat (rewrite kleisli_Eps).
  apply SB.
  repeat (rewrite <- kleisli_simpl).
  apply (BoolRelBFun _ _ H).
  eapply rhoBoolCompat.
  rewrite <- (@pred_nth_eq _ n0 x).
  rewrite H.
  rewrite kleisliVal.
  by simpl.
  rewrite <- (@pred_nth_eq _ m y).
  rewrite H0.
  rewrite kleisliVal.
  unfold _delta in H1. simpl in *. destruct (Unroll d') as [[n' | f'] | p].
  do 2 setoid_rewrite -> SUM_fun_simplx in H1. simpl in H1.
  apply vinj with (D:=nat_cpoType) in H1.
  do 2 setoid_rewrite -> SUM_fun_simplx.
  rewrite -> H1. simpl.
  destruct d. simpl.
  rewrite kleisliVal. by simpl. 
  rewrite kleisliVal. by simpl.
  do 2 setoid_rewrite -> SUM_fun_simplx in H1. simpl in H1.
  symmetry in H1. apply PBot_incon_eq in H1. inversion H1.
  setoid_rewrite -> SUM_fun_simplx in H1. simpl in H1.
  symmetry in H1. apply PBot_incon_eq in H1. inversion H1.
  eapply BoolRelBinFun with (f := f).
  reflexivity.
Qed.

Lemma RelBinFun f (n m : nat_cpoType) : forall r,
    r =-= f(n,m) -> ρ[nat̂] r (kleisli (eta <<  injnToDInf) r).
Proof.
  intros f n m. cofix RelBinFun.
  intros r equ.
  destruct r.
  rewrite kleisli_simpl; rewrite kleisli_Eps.
  rewrite <- kleisli_simpl.
  unfold _rho in RelBinFun.
  rewrite <- eq_Eps in equ.
  specialize (RelBinFun r equ).
  apply (SB RelBinFun).
  eapply rhoNatCompat.
  reflexivity.
  rewrite kleisliVal.
  unfold injnToDInf.
    by simpl.
    eapply SV with (n := 0) (m:=0).
    apply pred_nth_val.
    apply pred_nth_val.
    unfold _delta.
    simpl. rewrite URid.
    do 2 setoid_rewrite -> SUM_fun_simplx. auto.
Qed.

Lemma RelBFun f n : forall x y, ρ[nat̂] x y ->
  ρ[nat̂] ((kleisli (f << @PAIR nat_cpoType nat_cpoType n)) x)
   (kleisli (eta << injnToDInf)
            ((kleisli (f << PAIR nat_cpoType n))
               ((kleisli (VInfToNat << Unroll)) y))).
Proof.
  intros f n. cofix RelBFun. intros x y rel.
  inversion rel.
  repeat (rewrite kleisli_simpl).
  repeat (rewrite kleisli_Eps).
  apply SB.
  repeat (rewrite <- kleisli_simpl).
  apply (RelBFun _ _ H).
  eapply rhoNatCompat.
  rewrite <- (@pred_nth_eq _ n0 x).
  rewrite H.
  rewrite kleisliVal.
  by simpl.
  rewrite <- (@pred_nth_eq _ m y).
  rewrite H0.
  rewrite kleisliVal.
  unfold _delta in H1.
  rewrite -> H1.
  rewrite kleisliVal.
  by simpl.
  eapply RelBinFun with (f := f).
  reflexivity.
Qed.

Lemma deltaOrdOpP f : 
  forall d d' x x',
    ρ[nat̂] d x ->
    ρ[nat̂] d' x' ->
    ρ[bool̂] (kleisli (ev << <| KLEISLI , const _ d' |>)
                    (kleisli (eta << exp_fun f) d))
     (kleisli (kleisli (eta << (Roll << (in1 << in1 << B_to_N))) << ev <<
              <| KLEISLI , const _  ((kleisli VInfToNat
                                              ((kleisli (eta << Unroll)) x'))) |>)
              (kleisli (eta << exp_fun f) ((kleisli VInfToNat
                                              ((kleisli (eta << Unroll)) x))))).
Proof.
  intros f. cofix deltaOrdOpP. intros d d' x x' rel rel'.
  inversion rel.
  repeat (rewrite kleisli_simpl).
  repeat (rewrite kleisli_Eps).
  apply SB.
  repeat (rewrite <- kleisli_simpl).
  apply deltaOrdOpP.
  apply H.
  inversion rel'.
  repeat (rewrite kleisli_simpl).
  repeat (rewrite kleisli_Eps).
  apply SB.
  apply H2.
  eapply SV.
  apply H2.
  apply H3.
  apply H4. unfold _delta in H1.
  assert (d =-= Val d0).
  rewrite <- H.
    by rewrite pred_nth_eq.
  unfold _delta in H1.
  assert (x =-= Val (Roll (Unroll d'0))).
  apply tset_trans with (y := pred_nth x m).
  by rewrite pred_nth_eq.
  apply tset_trans with (y := Val (Roll (Unroll d'0))).
  rewrite H0.
  apply Val_stable. by rewrite RUid. auto.
  assert (((kleisli (ev << <| KLEISLI, const (SemType nat̂ -=> SemType bool̂ _BOT) d' |>)) ((kleisli (eta << exp_fun f)) d))
            =-=
            ((kleisli (ev << <| KLEISLI, const (SemType nat̂ -=> SemType bool̂ _BOT) d' |>)) ((kleisli (eta << exp_fun f)) (Val d0)))).
  by rewrite H4.
  setoid_rewrite kleisliVal in H6.
  simpl in H6.
  setoid_rewrite kleisliVal in H6.
  simpl in H6.
  eapply rhoBoolCompat.
    by rewrite H6.
    rewrite H5.
    unfold DInfToNat.
    rewrite kleisliVal.
    rewrite comp_simpl.
    rewrite URid.
    rewrite kleisliVal.
    rewrite -> H1.
    rewrite kleisliVal.
    simpl.
    rewrite kleisliVal.
    simpl.
    reflexivity.
  inversion rel'.
  repeat (rewrite kleisli_simpl).
  repeat (rewrite kleisli_Eps).
  2 : { unfold _delta in H9.
        assert (d' =-= Val  d1).
        rewrite <- H7. by rewrite pred_nth_eq.
        assert (x' =-= Val (Roll (Unroll d'1))).
        apply tset_trans with (y := pred_nth x' m0). by rewrite pred_nth_eq.
        apply tset_trans with (y := Val (Roll (Unroll d'1))).
        rewrite H8.
        apply Val_stable. by rewrite RUid. auto.
        eapply rhoBoolCompat.
        rewrite H12.
        rewrite kleisliVal. by simpl.
        rewrite H13.
        rewrite kleisliVal.
        rewrite comp_simpl.
        rewrite URid.
        rewrite kleisliVal.
        rewrite -> H9.
        rewrite kleisliVal.
        rewrite -> comp_assoc with (h:=Roll).
        assert ( Roll << (in1 << in1)
                      =-=
                      ((Roll << in1) << in1)
               ) by (by repeat rewrite -> comp_assoc).
        rewrite -> H14.
        repeat rewrite -> comp_assoc. by simpl.
        eapply OrdRelBinFun with (f := f).
        reflexivity.
  }
  apply SB.
  repeat (rewrite <- kleisli_simpl).
  eapply rhoBoolCompat.
  reflexivity.
  rewrite <- (comp_simpl (kleisli (eta << _))).
  rewrite <- (comp_simpl _ (kleisli (eta << Unroll))).
  rewrite -> comp_assoc with (h:=Roll).
  rewrite <- kleisli_comp2.
  assert ( Roll << (in1 << in1)
           =-=
           ((Roll << in1) << in1)
         ) by (by repeat rewrite -> comp_assoc).
  rewrite -> H10.
  repeat rewrite -> comp_assoc. by simpl.
  eapply OrdRelBFun with (f := f) (n := d0).
  apply H7.
Qed.

Lemma deltaBoolOpP f :
  forall d d' x x',
    ρ[bool̂] d x ->
    ρ[bool̂] d' x' ->
    ρ[bool̂] (kleisli (ev << <| KLEISLI , const _ d' |>)
                    (kleisli (eta << exp_fun f) d))
     (kleisli (kleisli (eta << (Roll << (in1 << in1 << B_to_N))) << ev <<
              <| KLEISLI , const _  ((kleisli VInfToBool
                                              ((kleisli (eta << Unroll)) x'))) |>)
              (kleisli (eta << exp_fun f) ((kleisli VInfToBool
                                              ((kleisli (eta << Unroll)) x))))).
Proof.
  intros f. cofix deltaBoolOpP. intros d d' x x' rel rel'.
  inversion rel.
  repeat (rewrite kleisli_simpl).
  repeat (rewrite kleisli_Eps).
  apply SB.
  repeat (rewrite <- kleisli_simpl).
  apply deltaBoolOpP.
  apply H.
  inversion rel'.
  repeat (rewrite kleisli_simpl).
  repeat (rewrite kleisli_Eps).
  apply SB.
  apply H2.
  eapply SV.
  apply H2.
  apply H3.
  apply H4.
  assert (d =-= Val d0).
  rewrite <- H.
    by rewrite pred_nth_eq.
  unfold _delta in H1.
  assert (x =-= Val d'0).
  rewrite <- H0.
    by rewrite pred_nth_eq.
  assert (((kleisli (ev << <| KLEISLI, const (SemType bool̂ -=> SemType bool̂ _BOT) d' |>)) ((kleisli (eta << exp_fun f)) d))
            =-=
            ((kleisli (ev << <| KLEISLI, const (SemType bool̂ -=> SemType bool̂ _BOT) d' |>)) ((kleisli (eta << exp_fun f)) (Val d0)))).
  by rewrite H4.
  setoid_rewrite kleisliVal in H6.
  simpl in H6.
  setoid_rewrite kleisliVal in H6.
  simpl in H6.
  eapply rhoBoolCompat.
    by rewrite H6.
    rewrite H5.
    rewrite kleisliVal.
    rewrite comp_simpl.
    rewrite kleisliVal.
    simpl in H1.
    destruct (Unroll d'0) as [[n' | f'] | p].
    do 2 setoid_rewrite -> SUM_fun_simplx in H1. simpl in H1.
    apply vinj with (D:=nat_cpoType) in H1.
    do 2 setoid_rewrite -> SUM_fun_simplx.
    rewrite -> H1. simpl.
    destruct d0. simpl.
    rewrite kleisliVal. by simpl. simpl.
    do 3 rewrite kleisliVal. by simpl.
    do 2 setoid_rewrite -> SUM_fun_simplx in H1. simpl in H1.
    symmetry in H1. apply PBot_incon_eq in H1. inversion H1.
    setoid_rewrite -> SUM_fun_simplx in H1. simpl in H1.
    symmetry in H1. apply PBot_incon_eq in H1. inversion H1.
    eapply rhoBoolCompat. reflexivity.
    rewrite kleisliVal. simpl. reflexivity.
  inversion rel'.
  repeat (rewrite kleisli_simpl).
  repeat (rewrite kleisli_Eps).
  2 : { unfold _delta in H9.
        assert (d' =-= Val  d1).
        rewrite <- H7. by rewrite pred_nth_eq.
        assert (x' =-= Val  d'1).
        rewrite <- H8. by rewrite pred_nth_eq.
        eapply rhoBoolCompat.
        rewrite H12.
        rewrite kleisliVal. by simpl.
        rewrite H13.
        rewrite kleisliVal.
        rewrite comp_simpl.
        simpl in H9.
        rewrite kleisliVal.
        destruct (Unroll d'1) as [[n' | f'] | p].
        do 2 setoid_rewrite -> SUM_fun_simplx in H9. simpl in H9.
        apply vinj with (D:=nat_cpoType) in H9.
        do 2 setoid_rewrite -> SUM_fun_simplx.
        rewrite -> H9. simpl.
        destruct d1. simpl.
        rewrite kleisliVal. by simpl. simpl.
        rewrite kleisliVal. by simpl.
        do 2 setoid_rewrite -> SUM_fun_simplx in H9. simpl in H9.
        symmetry in H9. apply PBot_incon_eq in H9. inversion H9.
        setoid_rewrite -> SUM_fun_simplx in H9. simpl in H9.
        symmetry in H9. apply PBot_incon_eq in H9. inversion H9.
        eapply rhoBoolCompat. reflexivity. by repeat (rewrite -> comp_assoc).
        eapply BoolRelBinFun with (f := f).
        reflexivity.
  }
  apply SB.
  repeat (rewrite <- kleisli_simpl).
  eapply rhoBoolCompat.
  reflexivity.
  rewrite <- (comp_simpl (kleisli (eta << _))).
  rewrite <- (comp_simpl _ (kleisli (eta << Unroll))).
  rewrite -> comp_assoc with (h:=Roll).
  rewrite <- kleisli_comp2.
  assert ( (Roll << (in1 << in1)) << B_to_N
           =-=
           ((Roll << in1) << in1) << B_to_N
         ) by (by repeat rewrite -> comp_assoc).
  rewrite -> H10.
  repeat rewrite -> comp_assoc. by simpl.
  eapply BoolRelBFun with (f := f) (n := d0).
  apply H7.
Qed.

Lemma deltaNatOpP f : 
  forall d d' x x',
    ρ[nat̂] d x ->
    ρ[nat̂] d' x' ->
    ρ[nat̂] (kleisli (ev << <| KLEISLI , const _ d' |>)
                    (kleisli (eta << exp_fun f) d))
     (kleisli (kleisli (eta << (Roll << (in1 << in1))) << ev <<
              <| KLEISLI , const _  ((kleisli VInfToNat
                                              ((kleisli (eta << Unroll)) x'))) |>)
              (kleisli (eta << exp_fun f) ((kleisli VInfToNat
                                              ((kleisli (eta << Unroll)) x))))).
Proof.
  intros f. cofix deltaNatOpP. intros d d' x x' rel rel'.
  inversion rel.
  repeat (rewrite kleisli_simpl).
  repeat (rewrite kleisli_Eps).
  apply SB.
  repeat (rewrite <- kleisli_simpl).
  apply deltaNatOpP.
  apply H.
  inversion rel'.
  repeat (rewrite kleisli_simpl).
  repeat (rewrite kleisli_Eps).
  apply SB.
  apply H2.
  eapply SV.
  apply H2.
  apply H3.
  apply H4.
  assert (d =-= Val d0).
  rewrite <- H.
    by rewrite pred_nth_eq.
  unfold _delta in H1.
  assert (x =-= Val (Roll (Unroll d'0))).
  apply tset_trans with (y := pred_nth x m).
  by rewrite pred_nth_eq.
  apply tset_trans with (y := Val (Roll (Unroll d'0))).
  rewrite H0.
  apply Val_stable. by rewrite RUid. auto.

  assert (((kleisli (ev << <| KLEISLI, const (SemType nat̂ -=> SemType nat̂ _BOT) d' |>)) ((kleisli (eta << exp_fun f)) d))
            =-=
            ((kleisli (ev << <| KLEISLI, const (SemType nat̂ -=> SemType nat̂ _BOT) d' |>)) ((kleisli (eta << exp_fun f)) (Val d0)))).
  by rewrite H4.
  setoid_rewrite kleisliVal in H6.
  simpl in H6.
  setoid_rewrite kleisliVal in H6.
  simpl in H6.
  eapply rhoNatCompat.
    by rewrite H6.
    rewrite H5.
    unfold DInfToNat.
    rewrite kleisliVal.
    rewrite comp_simpl.
    rewrite URid.
    rewrite kleisliVal.
    rewrite -> H1.
    rewrite kleisliVal.

    simpl.
    rewrite kleisliVal.
    simpl.
    reflexivity.
  inversion rel'.
  repeat (rewrite kleisli_simpl).
  repeat (rewrite kleisli_Eps).
  2 : { unfold _delta in H9.
        assert (d' =-= Val  d1).
        rewrite <- H7.
          by rewrite pred_nth_eq.
        assert (x' =-= Val (Roll (Unroll d'1))).
        apply tset_trans with (y := pred_nth x' m0). by rewrite pred_nth_eq.
        apply tset_trans with (y := Val (Roll (Unroll d'1))).
        rewrite H8.
        apply Val_stable. by rewrite RUid. auto.
        eapply rhoNatCompat.
        rewrite H12.
        rewrite kleisliVal. by simpl.
        rewrite H13.
        rewrite kleisliVal.
        rewrite comp_simpl.
        rewrite URid.
        rewrite kleisliVal.
        rewrite -> H9.
        rewrite kleisliVal.
        rewrite -> comp_assoc with (h:=Roll). by simpl.
        eapply RelBinFun with (f := f).
        reflexivity.
  }
  apply SB.
  repeat (rewrite <- kleisli_simpl).
  eapply rhoNatCompat.
  reflexivity.
  rewrite <- (comp_simpl (kleisli (eta << _))).
  rewrite <- (comp_simpl _ (kleisli (eta << Unroll))).
  rewrite -> comp_assoc with (h:=Roll).
  rewrite <- kleisli_comp2.
    by simpl.
  eapply RelBFun with (f := f) (n := d0).
  apply H7.
Qed.

Lemma rhoOrdOp f d d' x x' :
  ρ[nat̂] d x ->  ρ[nat̂] d' x' ->
  ρ[bool̂]
   (GenBinOpTy f (const _ d) (const _ d') ())
   (kleisli (eta << Roll) ((@GenOrdOp O f
                                      (const _ (kleisli (eta << Unroll) x))
                                      (const _ (kleisli (eta << Unroll) x')))
                             ())).
Proof.
  intros f d d' x x' rel rel'.
  eapply rhoBoolCompat.
  rewrite GenBinOpSimpl.
  unfold GenBinOpIn. simpl.
  reflexivity.
  rewrite ordopsimplE.
  simpl.
  repeat (setoid_rewrite <- comp_simpl).
  repeat (rewrite <- comp_assoc).
  rewrite <- kleisli_comp.
  do 6 rewrite comp_assoc. do 2 rewrite <- comp_assoc with (h:=eta).
  rewrite <- kleisli_comp2 with (g:=eta << Roll).
  rewrite -> kleisli_comp.
  simpl.
  repeat rewrite <- comp_assoc.
  repeat rewrite -> comp_assoc.
  assert ((((((eta << Roll) << in1) << in1)) << B_to_N)
            =-=
            (eta << (Roll << (in1 << in1 << B_to_N)))
         ) by (by repeat rewrite -> comp_assoc).
  rewrite -> H; clear H.
  reflexivity.
  apply (deltaOrdOpP (eta << SimpleBOp f) rel rel').
Qed.

Lemma rhoBoolOp f d d' x x' :
  ρ[bool̂] d x ->  ρ[bool̂] d' x' ->
  ρ[bool̂]
   (GenBinOpTy f (const _ d) (const _ d') ())
   (kleisli (eta << Roll) ((@GenBoolOp O f
                                      (const _ (kleisli (eta << Unroll) x))
                                      (const _ (kleisli (eta << Unroll) x')))
                             ())).
Proof.
  intros f d d' x x' rel rel'.
  eapply rhoBoolCompat.
  rewrite GenBinOpSimpl.
  unfold GenBinOpIn. simpl.
  reflexivity.
  rewrite boolopsimplE.
  simpl.
  repeat (setoid_rewrite <- comp_simpl).
  repeat (rewrite <- comp_assoc).
  rewrite <- kleisli_comp.
  do 6 rewrite comp_assoc. do 2 rewrite <- comp_assoc with (h:=eta).
  rewrite <- kleisli_comp2 with (g:=eta << Roll).
  rewrite -> kleisli_comp.
  simpl.
  repeat rewrite <- comp_assoc.
  repeat rewrite -> comp_assoc.
  assert ((((((eta << Roll) << in1) << in1)) << B_to_N)
            =-=
            (eta << (Roll << (in1 << in1 << B_to_N)))
         ) by (by repeat rewrite -> comp_assoc).
  rewrite -> H; clear H.
  reflexivity.
  apply (deltaBoolOpP (eta << SimpleBOp f) rel rel').
Qed.

Lemma rhoNatOp f d d' x x' :
  ρ[nat̂] d x ->  ρ[nat̂] d' x' ->
  ρ[nat̂]
   (GenBinOpTy f (const _ d) (const _ d') ())
   (kleisli (eta << Roll) ((@GenNatOp O f
                                      (const _ (kleisli (eta << Unroll) x))
                                      (const _ (kleisli (eta << Unroll) x')))
                             ())).
Proof.
  intros f d d' x x' rel rel'.
  eapply rhoNatCompat.
  rewrite GenBinOpSimpl.
  unfold GenBinOpIn. simpl.
  reflexivity.
  rewrite natopsimplE.
  simpl.
  repeat (setoid_rewrite <- comp_simpl).
  repeat (rewrite <- comp_assoc).
  rewrite <- kleisli_comp.
  do 5 rewrite comp_assoc. rewrite <- comp_assoc with (h:=eta).
  rewrite <- kleisli_comp2.
  rewrite <- (comp_assoc ((in1 << in1)) Roll).
  rewrite kleisli_comp. 
  repeat (rewrite comp_simpl).
    rewrite comp_assoc.
    reflexivity.
  apply (deltaNatOpP (eta << SimpleBOp f) rel rel').
Qed.

(* aplicación "conmuta" con toE *)
Lemma toEApp θ θ' : forall f d,
    (⇊ θ θ' f) (Roll (↓ θ d)) =-= kleisli (eta << Roll << toE θ') (f d).
Proof.
  intros θ θ' f d.
  simpl.
  setoid_replace (Unroll (Roll ((toE θ) d))) with ((toE θ) d).
  rewrite <- comp_simpl.
  rewrite kleisli_comp.
  rewrite <- (fst (EmbProjPair θ)).
  simpl.
  rewrite kleisliVal.
  by rewrite comp_simpl.
  rewrite <- comp_simpl.
  by rewrite UR_id.
Qed.

Lemma appCase : forall θ θ' f df z dz,
    δ[ θ ⇥ θ'] f df -> δ[ θ ] z dz -> 
    ρ[ θ' ] (f z) ((KLEISLIL ev (VInfToFun (Unroll df), dz))).
Proof.
  intros θ θ' f df z dz H H0. 
  destruct H as [g [equ H]].
  unfold _delta in H.
  fold _delta in H.
  eapply (snd (delta_rho_compat θ') (f z) (f z)  ((g dz)) _ (@tset_refl _ (f z))).
  rewrite equ.
  replace (Unroll (Roll (↑f g))) with ((Unroll << Roll) (↑f g)).
  rewrite UR_id.
  simpl. unfold id.
  do 2 rewrite SUM_fun_simplx.
  simpl.
  by rewrite KLEISLIL_unit2.
  by simpl.
  apply (H _ _ H0).
Qed.  

Lemma rho_strict : forall (θ : LType), ρ[θ] ⊥ ⊥.
Proof. intros θ; apply SBotIn.
Qed.

Lemma deltaBoolCComp : chain_complete δ[bool̂].
Proof.
  intros chs chs' chain_rhoV.
  unfold _delta.
  do 3 rewrite -> lub_comp_eq.
  apply lub_eq_compat.
  apply fmon_eq_intro.
  apply chain_rhoV.
Qed.

Lemma rhoBoolCComp : chain_complete ρ[bool̂].
Proof.
    apply (SEChainComplete deltaBoolCompat deltaBoolCComp).
Qed.

Lemma deltaNatCComp : chain_complete δ[nat̂].
Proof.
    intros chs chs' chain_rhoV.
    simpl in *.
    do 2 rewrite -> lub_comp_eq. setoid_rewrite -> lub_comp_eq with (f:=eta).
    apply lub_eq_compat.
    apply fmon_eq_intro.
    apply chain_rhoV.
Qed.

Lemma rhoNatCComp : chain_complete ρ[nat̂].
Proof.
    apply (SEChainComplete deltaNatCompat deltaNatCComp).
Qed.

Lemma RollInjle x y : Roll x <= Roll y -> x <= y.
Proof. intros x y H.
       apply Ole_trans with (y := (Unroll << Roll) x).
       by rewrite UR_id.
       apply Ole_trans with (y := (Unroll << Roll) y).
       do 2 rewrite comp_simpl.
       apply fmonotonic.
       apply H.
         by rewrite UR_id.
Qed.

Lemma deltaPairCComp : forall (θ1 θ2 : LType),
    chain_complete δ[θ1] ->
    chain_complete δ[θ2] ->
    chain_complete δ[θ1 ⨱ θ2].
Proof.
  intros θ1 θ2 IH1 IH2 chs chs' chain_rhoV.
  assert (lub chs'  =-= Roll (Unroll (lub chs' ))) by
      (rewrite RUid ; by symmetry ).
  destruct (Unroll (lub chs' )) as [[k | g] | p].
  destruct (chain_rhoV 0) as [f [eq [? ?]]].
  pose proof (le_lub chs' 0) as leq.
  setoid_rewrite -> H0 in leq.
  setoid_rewrite H in leq.
  apply RollInjle in leq.
  inversion leq.
  destruct (chain_rhoV 0) as [f [eq [? ?]]].
  pose proof (le_lub chs' 0) as leq.
  setoid_rewrite -> H0 in leq.
  setoid_rewrite H in leq.
  apply RollInjle in leq.
  inversion leq.
  destruct p as [pv1 pv2].
  exists pv1, pv2. split. auto.
  simpl.
  unfold chain_complete in IH1.
  simpl in chain_rhoV.
  assert  (forall (i : natO),
              exists (pi : DInf * DInf), chs' i =-= Roll ↑p pi /\ pi <= (pv1,pv2)).
  intros i. specialize (chain_rhoV i).
  destruct chain_rhoV as [pv1' [pv2' [? [? ?]]]].
  exists (pv1', pv2'). split. auto.
  assert (chs' i =-= Roll (Unroll ( chs' i))) by
      (rewrite RUid ; by symmetry).
  pose proof (le_lub chs' i) as leq.
  setoid_rewrite H in leq.
  setoid_rewrite H0 in leq.
  apply RollInjle in leq.
  apply leq.
  set (chss :=  (fun n => [|[| const _ (pv1, pv2), const _ (pv1, pv2)|], Id |]
                        (Unroll (chs' n)))).
  assert (monotonic chss). 
  - unfold monotonic.
    intros n m leq.
    unfold chss.
    destruct (H0 n) as [fn [eqn _]].
    destruct (H0 m) as [fm [eqm _]].
    rewrite eqn. rewrite eqm.
    rewrite URid.
    rewrite URid.
    simpl ; unfold id; simpl.  
    rewrite SUM_fun_simplx; rewrite SUM_fun_simplx.
    simpl ;  unfold id.
    assert (chs' n <= chs' m).
      by apply fmonotonic.
    setoid_rewrite eqn in H1; setoid_rewrite eqm in H1.
    apply RollInjle in H1.
    apply H1.
  set (chssp := mk_fmono H1).
  assert (forall i, chs' i =-= Roll (inPair (chssp i))).
  - intro i.
    simpl.
    destruct (H0  i) as [pi [eq _]].
    rewrite eq.
    unfold chss.
    apply monotonic_stable.
    auto. simpl.
    apply monotonic_stable.
    auto.
    rewrite eq.
    rewrite URid.
    simpl; unfold id; simpl.
    rewrite SUM_fun_simplx.
    auto.
  assert(eql : lub chssp =-= (pv1, pv2)).
  - assert ((Roll (↑p (pv1, pv2)))
              =-=
            (Roll << in2) (lub chssp)
           ).
    rewrite -> lub_comp_eq. simpl.
    eapply tset_trans. rewrite <- H. reflexivity.
    apply lub_eq_compat. split. simpl.
    apply H2. intro i. rewrite -> (H2 i). auto.
    simpl in H3.
    apply RollInj in H3. symmetry. apply H3.
  - assert (pi1 (A:=DInf) (B:=DInf) (lub chssp) =-= pv1).
      by rewrite -> eql.
  - assert (pi2 (A:=DInf) (B:=DInf) (lub chssp) =-= pv2).
      by rewrite -> eql.
  split.
  - Case "δ[θ1]".
    eapply (fst (delta_rho_compat θ1)).
    reflexivity.
    apply H3.
    simpl.
    apply IH1.
    intro i.
    specialize (chain_rhoV i).
    destruct chain_rhoV as [pv1' [pv2' [? [? ?]]]].
    simpl.
    specialize (H2 i). rewrite -> H5 in H2. simpl in H2.
    -- assert (pi1 (A:=DInf) (B:=DInf) (chss i) =-= pv1').
       apply RollInj in H2. eapply tset_trans.
       apply fmon_eq_compat. reflexivity. symmetry. apply H2. auto.
       simpl in H7.
    eapply (fst (delta_rho_compat θ1)).
    reflexivity. symmetry.
    apply H8.
    apply H6.
  - Case "δ[θ2]".
    eapply (fst (delta_rho_compat θ2)).
    reflexivity.
    apply H4.
    simpl.
    apply IH2.
    intro i.
    specialize (chain_rhoV i).
    destruct chain_rhoV as [pv1' [pv2' [? [? ?]]]].
    simpl.
    specialize (H2 i). rewrite -> H5 in H2. simpl in H2.
    -- assert (pi2 (A:=DInf) (B:=DInf) (chss i) =-= pv2').
       apply RollInj in H2. eapply tset_trans.
       apply fmon_eq_compat. reflexivity. symmetry. apply H2. auto.
       simpl in H7.
    eapply (fst (delta_rho_compat θ2)).
    reflexivity. symmetry.
    apply H8.  
    apply H7.
Qed.

Lemma fromRel θ1 θ2 f x : δ[θ1 ⇥ θ2] f x -> exists g, x =-= Roll (↑f g). 
Proof.
  intros θ1 θ2 f x H.
  destruct H as [g [eq _]].
  by exists g.
Qed.

Lemma deltaArrCComp θ1 θ2:
  chain_complete δ[θ1] ->
  chain_complete δ[θ2] ->
  chain_complete δ[θ1 ⇥ θ2].
Proof.
  intros θ1 θ2 ccδ1 ccδ2.
  intros chs chs' allRel.
  simpl.
  assert (lub chs'  =-= Roll (Unroll (lub chs' ))) by
      (rewrite RUid ; by symmetry ).
  destruct (Unroll (lub chs' )) as [[k | g] | p].
  destruct (allRel 0) as [f [eqf rel]].
  pose proof (le_lub chs' 0) as leq.
  setoid_rewrite eqf in leq.
  setoid_rewrite H in leq . 
  apply RollInjle in leq.
  inversion leq.
  exists g. split. assumption.
  intros v d rel.
  assert (H0 : forall i, exists fi, chs' i =-= Roll (↑f fi) /\ fi <= g).
  intro i.
  destruct (allRel i) as [fi [eqfi relfi]].
  assert (chs' i =-= Roll (Unroll ( chs' i))) by
      (rewrite RUid ; by symmetry).
  destruct (Unroll ( chs' i)) as [[k | h] | p].
  setoid_rewrite eqfi in H0.
  apply RollInj in H0.
  destruct H0 as [abs _].
  inversion abs.
  exists h. split. assumption.
  pose proof (le_lub chs' i) as leq.
  setoid_rewrite H in leq.
  setoid_rewrite H0 in leq.
  apply RollInjle in leq.
  apply leq.
  setoid_rewrite eqfi in H0.
  apply RollInj in H0.
  destruct H0 as [abs _].
  inversion abs.
  set (chss :=  (fun n => [| [|const _ (const _ PBot) ,
                         Id |], const _ (const _ PBot)|] (Unroll (chs' n)))).
  assert (monotonic chss). 
  unfold monotonic.
  intros n m leq.
  unfold chss.
  destruct (H0 n) as [fn [eqn _]].
  destruct (H0 m) as [fm [eqm _]].
  rewrite eqn. rewrite eqm.
  rewrite URid.
  rewrite URid.
  simpl ; unfold id; simpl.
  do 2 rewrite SUM_fun_simplx; do 2 rewrite SUM_fun_simplx.
  simpl ;  unfold id.
  assert (chs' n <= chs' m).
  by apply fmonotonic.
  setoid_rewrite eqn in H1; setoid_rewrite eqm in H1.
  apply RollInjle in H1.
  apply H1.
  set (chssf := mk_fmono H1).
  assert (forall (i : nat_cpoType), chs' i =-= Roll (↑f (chssf i))).
  intro i.
  simpl.
  destruct (H0  i) as [fi [eq _]].
  rewrite eq.
  unfold chss.
  apply monotonic_stable.
  auto. simpl.
  assert ((@INL (nat_cpoType + (DInf -=> DInf _BOT)) (DInf * DInf))
            (@INR (nat_cpoType) (DInf -=> DInf _BOT)
                  fi) =-= inl (inr fi)). auto.
  rewrite <- H2; clear H2.
  apply monotonic_stable.
  auto.
  apply monotonic_stable.
  auto.
  rewrite eq.
  rewrite URid.
  simpl; unfold id; simpl.
  do 2 rewrite SUM_fun_simplx.
  auto.
  assert(eql : lub chssf =-=  g).
  split.
  apply lub_le.
  intro i.
  simpl.
  specialize (H2 i).
  destruct (H0 i) as [fi [eq leq]].
  setoid_rewrite H2 in eq.
  apply RollInj in eq.
  apply Ole_trans with (y := fi ).
  apply eq. apply leq.
  simpl.
  assert ((Roll (↑f g)) <= (Roll (↑f (lub (mk_fmono H1))))).
  rewrite <- H.
  apply lub_le.
  intro i.
  rewrite (H2 i).
  apply fmonotonic.
  assert (chssf i <= lub chssf).
  apply le_lub.
  apply H3.
  apply (RollInjle H3).
  apply (SEStableR (fst (delta_rho_compat θ2))) with (y := (lub chssf) d).
  apply (SEChainComplete (fst (delta_rho_compat θ2)) ccδ2).
  intro i.
  simpl.
  specialize (allRel i).
  clear H0.
  destruct allRel as [fi [eqi reli]].
  apply (SEStableR (fst (delta_rho_compat θ2))) with (y := fi d).
  apply reli.
  apply rel.
  assert (fi =-= chssf i).
  specialize (H2 i).
  setoid_rewrite eqi in H2.
  apply RollInj in H2.
  apply H2.
  by rewrite H0.
  by rewrite eql.
  destruct (allRel 0) as [f [eqf rel]].
  pose proof (le_lub chs' 0) as leq.
  setoid_rewrite eqf in leq.
  setoid_rewrite H in leq . 
  apply RollInjle in leq.
  inversion leq.
Qed.

Lemma delta_rho_cc (θ : LType): (chain_complete δ[θ]) /\ (chain_complete ρ[θ]).
Proof.
  intros θ.
  induction θ.
  - split.
    + apply deltaBoolCComp.
    + apply (SEChainComplete deltaBoolCompat deltaBoolCComp).
  - split.
    + apply deltaNatCComp. 
    + apply (SEChainComplete deltaNatCompat deltaNatCComp).
  - split.
    + apply (deltaArrCComp (fst IHθ1) (fst IHθ2)).
    + apply (SEChainComplete
               (fst (delta_rho_compat (θ1 ⇥ θ2)))
               (deltaArrCComp  (fst IHθ1)  (fst IHθ2))).
  - split.
    + apply (deltaPairCComp (fst IHθ1) (fst IHθ2)).
    + apply (SEChainComplete
               (fst (delta_rho_compat (θ1 ⨱ θ2)))
               (deltaPairCComp  (fst IHθ1)  (fst IHθ2))).
Qed.

Lemma BTONInj b b' : B_to_N b =-= B_to_N b' -> b =-= b'.
Proof.
  intros b b' H.
  destruct b.
  destruct b'. auto.
  simpl in H. inversion H. inversion H0.
  destruct b'.
  simpl in H. inversion H. inversion H0.
  auto.
Qed.

Definition rhoV_E_In θ := forall (x : SemType θ), δ[θ] x (Roll (toE θ x)).
Definition rhoV_To_I_Leq θ := forall (x : SemType θ) (y : DInf),
    δ[θ] x y -> (toI θ << Unroll) y <= eta x.
Definition rhoV_To_I_Geq θ := forall (x : SemType θ) (y : DInf),
    δ[θ] x y -> eta x <= (toI θ << Unroll) y.
Definition rhoV_To_I_Eq θ := forall (x : SemType θ) (y : DInf),
    δ[θ] x y -> (toI θ << Unroll) y =-= eta x.

Definition rhoE_E_In θ  := forall (x : SemType θ _BOT),
    ρ[θ] x (kleisli (eta << Roll << toE θ) x).
Definition  rhoE_To_I_Leq θ := forall (x : SemType θ _BOT) (y : DInf _BOT),
    ρ[θ] x y -> kleisli (toI θ << Unroll) y <= x.
Definition  rhoE_To_I_Geq θ := forall (x : SemType θ _BOT) (y : DInf _BOT),
    ρ[θ] x y -> x <= kleisli (toI θ << Unroll) y.
Definition  rhoE_To_I_Eq θ := forall (x : SemType θ _BOT) (y : DInf _BOT),
    ρ[θ] x y -> kleisli (toI θ << Unroll) y =-= x.

Lemma rhoV_E_In_Bool : rhoV_E_In bool̂.
Proof.
  intro.
  unfold _delta. simpl.
  rewrite -> URid.
  do 2 setoid_rewrite -> SUM_fun_simplx. auto.
Qed.

Lemma rhoE_E_In_Bool : rhoE_E_In bool̂.
Proof.
  cofix rhoE_E_In_Bool. intro x.
  destruct x as [x' | v].
  rewrite kleisli_simpl; rewrite kleisli_Eps; rewrite <- kleisli_simpl.
  apply SB. apply rhoE_E_In_Bool.
  rewrite kleisli_simpl; rewrite kleisli_Val.
  simpl.
  apply SV with (n := 0) (d := v) (d':=Roll (inNat (B_to_N v))) (m := 0) .
  by simpl. by simpl.
  apply rhoV_E_In_Bool.
Qed.

Lemma rhoV_E_In_Nat : rhoV_E_In nat̂.
Proof. intro. simpl. rewrite -> URid. by do 2 setoid_rewrite -> SUM_fun_simplx. Qed.

Lemma rhoE_E_In_Nat : rhoE_E_In nat̂.
Proof.
  cofix rhoE_E_In_Nat. intro x.
  destruct x as [x' | v].
  rewrite kleisli_simpl; rewrite kleisli_Eps; rewrite <- kleisli_simpl.
  apply SB. apply rhoE_E_In_Nat.
  rewrite kleisli_simpl; rewrite kleisli_Val.
  simpl.
  apply SV with (n := 0) (d := v) (d':=Roll (inNat v)) (m := 0) .
  by simpl. by simpl.
 apply rhoV_E_In_Nat.
Qed.

Lemma rhoV_E_In_Arr (θ1 θ2 : LType) :
  rhoE_E_In θ2 ->
  rhoV_To_I_Eq θ1 ->
  rhoV_E_In (θ1 ⇥ θ2).
Proof.
  intros θ1 θ2 HI2 HI1 f.
  simpl.
  exists (toEArr θ1 θ2 f).
  split.
  unfold toEArr.
  by simpl.
  intros v d rel. simpl.
  apply HI1 in rel.
  eapply (snd (delta_rho_compat θ2 ) _ _ _ _ (tset_refl (f v))). simpl in rel.
  rewrite rel. rewrite kleisliVal. apply tset_refl.
  apply HI2.
Qed.

Lemma rhoE_E_In_Arr θ1 θ2 :
  rhoE_E_In θ2 ->
  rhoV_To_I_Eq θ1 ->
  rhoE_E_In (θ1 ⇥ θ2).
Proof.
  intros θ1 θ2 HI1 HI2. cofix rhoE_E_In_Arr. intro x.
  destruct x as [x' | f].
  rewrite kleisli_simpl; rewrite kleisli_Eps; rewrite <- kleisli_simpl.
  apply SB. apply rhoE_E_In_Arr.
  rewrite kleisli_simpl; rewrite kleisli_Val.
  eapply SV with (n := 0) (m := 0).
  by simpl.
  by simpl.   
  apply rhoV_E_In_Arr.
  apply HI1. apply HI2. 
Qed.

(* Este lema es super útil y debería usarlo más en pruebas de más arriba. *)
Lemma VInfToNat_prop : forall d m, VInfToNat d =-= eta m -> d =-= inNat m.
Proof.
  intros d m H.
  destruct d as [[n | f] | p].
  do 2 setoid_rewrite -> SUM_fun_simplx in H.
  apply vinj with (D:=nat_cpoType) in H. auto.
  do 2 setoid_rewrite -> SUM_fun_simplx in H. simpl in H.
  apply tset_sym in H. apply PBot_incon_eq in H. contradiction.
  setoid_rewrite -> SUM_fun_simplx in H. simpl in H.
  apply tset_sym in H. apply PBot_incon_eq in H. contradiction.
Qed.

Lemma rhoE_To_I_Leq_Bool : rhoE_To_I_Leq bool̂.
Proof.
  cofix rhoE_To_I_Leq_Bool.
  intros x y H.
  inversion H.
  - Case "SB".
    rewrite kleisli_simpl; rewrite kleisli_Eps; rewrite <- kleisli_simpl.
    apply DLleEps. apply rhoE_To_I_Leq_Bool. assumption.
  - Case "SVar".
    have ValExist := Val_exists_pred_eq (ex_intro _ n H0); rewrite <- ValExist.
    have ValExist' := Val_exists_pred_eq (ex_intro _ m H1); rewrite <- ValExist'.
    rewrite kleisliVal. simpl in *. 
    destruct d. simpl in H2. apply VInfToNat_prop with (d:=Unroll d') in H2.
    rewrite -> H2. simpl. by do 2 rewrite SUM_fun_simplx; simpl.
    simpl in H2. apply VInfToNat_prop with (d:=Unroll d') in H2.
    rewrite -> H2. simpl. by do 2 rewrite SUM_fun_simplx; simpl.
Qed.

Lemma rhoE_To_I_Geq_Bool : rhoE_To_I_Geq bool̂.
Proof.
  cofix rhoE_To_I_Geq_Bool.
  intros x y H.
  inversion H.
  - Case "SBot".
    rewrite kleisli_simpl; rewrite kleisli_Eps; rewrite <- kleisli_simpl.
    apply DLleEps. apply rhoE_To_I_Geq_Bool. assumption.
  - Case "SVar".
    have ValExist := Val_exists_pred_eq (ex_intro _ n H0); rewrite <- ValExist.
    have ValExist' := Val_exists_pred_eq (ex_intro _ m H1); rewrite <- ValExist'.
    rewrite kleisliVal. simpl in *.
    destruct d. simpl in H2. apply VInfToNat_prop with (d:=Unroll d') in H2.
    rewrite -> H2. simpl. by do 2 rewrite SUM_fun_simplx; simpl.
    simpl in H2. apply VInfToNat_prop with (d:=Unroll d') in H2.
    rewrite -> H2. simpl. by do 2 rewrite SUM_fun_simplx; simpl.
Qed.

Lemma rhoE_To_I_Eq_Bool : rhoE_To_I_Eq bool̂.
Proof.
  intros x y H.
  apply Ole_antisym.
  apply rhoE_To_I_Leq_Bool. assumption.
  apply rhoE_To_I_Geq_Bool. assumption.
Qed.

Lemma rhoE_To_I_Leq_Nat : rhoE_To_I_Leq nat̂.
Proof.
  cofix rhoE_To_I_Leq_Nat.
  intros x y H.
  inversion H.
  - Case "SB".
    rewrite kleisli_simpl; rewrite kleisli_Eps; rewrite <- kleisli_simpl.
    apply DLleEps. apply rhoE_To_I_Leq_Nat. assumption.
  - Case "SVar".
    have ValExist := Val_exists_pred_eq (ex_intro _ n H0); rewrite <- ValExist.
    have ValExist' := Val_exists_pred_eq (ex_intro _ m H1); rewrite <- ValExist'.
    rewrite kleisliVal. simpl in *. rewrite <- H2. auto. 
Qed.

Lemma rhoE_To_I_Geq_Nat : rhoE_To_I_Geq nat̂.
Proof.
  cofix rhoE_To_I_Geq_Nat.
  intros x y H.
  inversion H.
  - Case "SBot".
    rewrite kleisli_simpl; rewrite kleisli_Eps; rewrite <- kleisli_simpl.
    apply DLleEps. apply rhoE_To_I_Geq_Nat. assumption.
  - Case "SVar".
    have ValExist := Val_exists_pred_eq (ex_intro _ n H0); rewrite <- ValExist.
    have ValExist' := Val_exists_pred_eq (ex_intro _ m H1); rewrite <- ValExist'.
    rewrite kleisliVal. simpl in *. rewrite <- H2. auto. 
Qed.

Lemma rhoE_To_I_Eq_Nat : rhoE_To_I_Eq nat̂.
Proof.
  intros x y H.
  apply Ole_antisym.
  apply rhoE_To_I_Leq_Nat. assumption.
  apply rhoE_To_I_Geq_Nat. assumption.
Qed.

Lemma rhoE_To_I_Leq_Arr  (θ1 θ2 : LType) :
  rhoV_E_In θ1 ->
  rhoE_To_I_Leq θ2 ->
  rhoE_To_I_Leq θ1 ⇥ θ2.
Proof.
  cofix rhoE_To_I_Leq_Arr. intros θ1 θ2 H H0 x y H1.
  inversion H1.
  rewrite kleisli_simpl. rewrite kleisli_Eps. rewrite <- kleisli_simpl.
  apply DLleEps. apply rhoE_To_I_Leq_Arr. assumption. assumption.
  assumption.
  have bla := Val_exists_pred_eq
               (ex_intro (fun n => pred_nth x n = Val d) n H2).

  have bla' := Val_exists_pred_eq
               (ex_intro (fun n => pred_nth y n = Val d') m H3).
  rewrite <- bla. rewrite <- bla'. rewrite kleisliVal. simpl.
  destruct H4 as [f [? ?]].
  rewrite H4. rewrite URid.
  do 2 setoid_rewrite -> SUM_fun_simplx.  
  simpl.
  apply Val_le_compat.
  intro a. simpl. unfold id.
  rewrite <- comp_simpl. unfold KUR.
  rewrite <- kleisli_comp2.
  apply H0. apply H7.
  apply H.
Qed.

Lemma rhoE_To_I_Geq_Arr  (θ1 θ2 : LType) :
  rhoV_E_In θ1 ->
  rhoE_To_I_Geq θ2 ->
  rhoE_To_I_Geq θ1 ⇥ θ2.
Proof.
  cofix rhoE_To_I_Geq_Arr. intros θ1 θ2 H H0 x y H1.
  inversion H1.
  rewrite kleisli_simpl. rewrite kleisli_Eps. rewrite <- kleisli_simpl.
  apply DLleEps. apply rhoE_To_I_Geq_Arr. assumption. assumption.
  assumption.
  have bla := Val_exists_pred_eq
               (ex_intro (fun n => pred_nth x n = Val d) n H2).

  have bla' := Val_exists_pred_eq
               (ex_intro (fun n => pred_nth y n = Val d') m H3).
  rewrite <- bla. rewrite <- bla'. rewrite kleisliVal. simpl.
  destruct H4 as [f [? ?]].
  rewrite H4. rewrite URid.
  do 2 setoid_rewrite -> SUM_fun_simplx.  
  simpl.
  apply Val_le_compat.
  intro a. simpl. unfold id.
  rewrite <- comp_simpl. unfold KUR. rewrite <- kleisli_comp2.
  apply H0. apply H7.
  apply H.
Qed.

Lemma rhoE_To_I_Eq_Arr (θ1 θ2 : LType) :
  rhoV_E_In θ1 ->
  rhoE_To_I_Eq θ2 ->
  rhoE_To_I_Eq θ1 ⇥ θ2.
Proof.
  intros θ1 θ2 H H0 x y H1.
  apply Ole_antisym.
  apply rhoE_To_I_Leq_Arr. assumption. unfold rhoE_To_I_Eq in H0.
  unfold rhoE_To_I_Leq. apply H0. assumption.
  apply rhoE_To_I_Geq_Arr. assumption. unfold rhoE_To_I_Eq in H0.
  unfold rhoE_To_I_Geq. apply H0. assumption.
Qed.

Lemma rhoV_To_I_Eq_Bool : rhoV_To_I_Eq bool̂.
Proof.
  intros x y H.
  simpl in H.
  destruct x. simpl in H. apply VInfToNat_prop in H. simpl. rewrite -> H.
  by do 2 setoid_rewrite SUM_fun_simplx; simpl.
  simpl in H. apply VInfToNat_prop in H. simpl. rewrite -> H.
  by do 2 setoid_rewrite SUM_fun_simplx; simpl.
Qed.

Lemma rhoV_To_I_Eq_Nat : rhoV_To_I_Eq nat̂.
Proof.
  intros x y H.
  simpl in H.
  rewrite <- H.
  rewrite <- comp_simpl. auto. 
Qed.

Lemma rhoV_To_I_Leq_Arr (θ1 θ2 : LType) :
  rhoV_E_In θ1 ->
  rhoE_To_I_Leq θ2 ->
  rhoV_To_I_Leq (θ1 ⇥ θ2).
Proof.
  intros θ1 θ2 Ha HI x y H.
  destruct H as [? [? ?]].
  rewrite H.
  simpl.
  rewrite <- comp_simpl with (f:=Unroll).
  rewrite UR_id; simpl; unfold id.
  do 2 rewrite SUM_fun_simplx; simpl.
  apply Val_le_compat.
  intro a. simpl. unfold id.
  specialize (H0 _ _ (Ha a)).
  specialize (HI _ _ H0).
  rewrite <- comp_simpl. unfold KUR.
  rewrite <- kleisli_comp2.
  apply HI.
Qed.

Lemma rhoV_To_I_Geq_Arr (θ1 θ2 : LType) :
  rhoV_E_In θ1 ->
  rhoE_To_I_Geq θ2 ->
  rhoV_To_I_Geq (θ1 ⇥ θ2).
Proof.
  intros θ1 θ2 H H0 x y H1.
  destruct H1 as [f [? ?]]. rewrite H1.
  simpl. rewrite URid. 
  do 2 rewrite SUM_fun_simplx; simpl.
  apply Val_le_compat.
  intro a. simpl. unfold id. rewrite <- comp_simpl. unfold KUR.
  rewrite <- kleisli_comp2.
  apply H0.
  apply H2. apply H.
Qed.

Lemma rhoV_To_I_Eq_Arr (θ1 θ2 : LType) :
  rhoV_E_In θ1 ->
  rhoE_To_I_Eq θ2 ->
  rhoV_To_I_Eq θ1 ⇥ θ2.
Proof.
  intros θ1 θ2 H H0 x y H1.
  apply Ole_antisym.
  apply rhoV_To_I_Leq_Arr. assumption. unfold rhoE_To_I_Eq in H0.
  unfold rhoE_To_I_Leq. apply H0. assumption.
  apply rhoV_To_I_Geq_Arr. assumption. unfold rhoE_To_I_Eq in H0.
  unfold rhoE_To_I_Geq. apply H0. assumption.
Qed.

Lemma rhoV_E_In_Pair (θ1 θ2 : LType) :
  rhoV_E_In θ1 ->
  rhoV_E_In θ2 ->
  rhoV_E_In (θ1 ⨱ θ2).
Proof.
  intros θ1 θ2 IH1 IH2 (a,b).
  simpl.
  exists (Roll (↓ θ1 a)), (Roll (↓ θ2 b)). split. auto.
  split. auto. auto.
Qed.

Lemma rhoV_To_I_Eq_Pair (θ1 θ2 : LType) :
  rhoV_To_I_Eq θ1 ->
  rhoV_To_I_Eq θ2 ->
  rhoV_To_I_Eq θ1 ⨱ θ2.
Proof.
  intros θ1 θ2 IH1 IH2 (a,b) d H1.
  destruct H1 as [pv1 [pv2 [? [? ?]]]].
  rewrite <- (RUid d) in *. simpl in H.
  destruct (Unroll d) as [[n | f] | [pv1' pv2']]; apply RollInj in H.
  - Case "nat".
    inversion H. inversion H2.
  - Case "θ1 ⇥ θ2".
    inversion H. inversion H2.
  - Case "θ1 ⨱ θ2".
    simpl. rewrite -> URid. simpl.
    setoid_rewrite -> SUM_fun_simplx. simpl in *.
    have IH1' := IH1 _ _ H0; simpl in IH1'.
    have IH2' := IH2 _ _ H1; simpl in IH2'.
    -- assert (pv1 =-= pv1').
       apply tset_trans with (y:=pi1 (A:=DInf) (pv1,pv2)). auto.
       symmetry.
       apply tset_trans with (y:=pi1 (A:=DInf) (pv1',pv2')). auto.
       apply fmon_eq_compat. reflexivity. apply H.
    -- assert (pv2 =-= pv2').
       apply tset_trans with (y:=pi2 (A:=DInf) (pv1,pv2)). auto.
       symmetry.
       apply tset_trans with (y:=pi2 (A:=DInf) (pv1',pv2')). auto.
       apply fmon_eq_compat. reflexivity. apply H.
    rewrite <- H2, <- H3; clear H2 H3.
    rewrite -> IH1', -> IH2'.
    apply Smash_ValVal.
Qed.

Lemma rhoE_E_In_Pair θ1 θ2 :
  rhoV_E_In θ1 ->
  rhoV_E_In θ2 ->
  rhoE_E_In (θ1 ⨱ θ2).
Proof.
  intros θ1 θ2 IH1 IH2.
  cofix rhoE_E_In_Pair. intro x.
  destruct x as [x' | [a b]].
  rewrite kleisli_simpl; rewrite kleisli_Eps; rewrite <- kleisli_simpl.
  apply SB. apply rhoE_E_In_Pair.
  rewrite kleisli_simpl; rewrite kleisli_Val.
  eapply SV with (n := 0) (m := 0). by simpl. by simpl.   
  apply rhoV_E_In_Pair.
  apply IH1. apply IH2. 
Qed.

Lemma rhoE_To_I_Geq_Pair  (θ1 θ2 : LType) :
  rhoV_To_I_Eq θ1 ->
  rhoV_To_I_Eq θ2 ->
  rhoE_To_I_Geq θ1 ⨱ θ2.
Proof.
  cofix rhoE_To_I_Geq_Pair. intros θ1 θ2 IH1 IH2 x y H1.
  inversion H1.
  rewrite kleisli_simpl. rewrite kleisli_Eps. rewrite <- kleisli_simpl.
  apply DLleEps. apply rhoE_To_I_Geq_Pair. assumption. assumption.
  assumption.
  have bla := Val_exists_pred_eq
               (ex_intro (fun n => pred_nth x n = Val d) n H).
  have bla' := Val_exists_pred_eq
                (ex_intro (fun n => pred_nth y n = Val d') m H0).
  rewrite <- bla. rewrite <- bla'. rewrite kleisliVal. simpl.
  destruct H2 as [pv1 [pv2 [? [? ?]]]].
  rewrite <- (RUid d') in *.
  destruct (Unroll d') as [[i | f] | [pv1' pv2']]; apply RollInj in H2.
  inversion H2. inversion H7.
  inversion H2. inversion H7.
  rewrite -> URid.
  setoid_rewrite -> SUM_fun_simplx. destruct d as [a b]. simpl in *.
  have IH1' := IH1 _ _ H5; simpl in IH1'.
  have IH2' := IH2 _ _ H6; simpl in IH2'.
  -- assert (pv1 =-= pv1').
     apply tset_trans with (y:=pi1 (A:=DInf) (pv1,pv2)). auto.
     symmetry.
     apply tset_trans with (y:=pi1 (A:=DInf) (pv1',pv2')). auto.
     apply fmon_eq_compat. reflexivity. apply H2.
  -- assert (pv2 =-= pv2').
     apply tset_trans with (y:=pi2 (A:=DInf) (pv1,pv2)). auto.
     symmetry.
     apply tset_trans with (y:=pi2 (A:=DInf) (pv1',pv2')). auto.
     apply fmon_eq_compat. reflexivity. apply H2.
  rewrite <- H7, <- H8; clear H7 H8.
  rewrite -> IH1', -> IH2'.
  apply Smash_ValVal.
Qed.

Lemma rhoE_To_I_Leq_Pair  (θ1 θ2 : LType) :
  rhoV_To_I_Eq θ1 ->
  rhoV_To_I_Eq θ2 ->
  rhoE_To_I_Leq θ1 ⨱ θ2.
Proof.
  cofix rhoE_To_I_Leq_Pair. intros θ1 θ2 IH1 IH2 x y H1.
  inversion H1.
  rewrite kleisli_simpl. rewrite kleisli_Eps. rewrite <- kleisli_simpl.
  apply DLleEps. apply rhoE_To_I_Leq_Pair. assumption. assumption.
  assumption.
  have bla := Val_exists_pred_eq
               (ex_intro (fun n => pred_nth x n = Val d) n H).
  have bla' := Val_exists_pred_eq
                (ex_intro (fun n => pred_nth y n = Val d') m H0).
  rewrite <- bla. rewrite <- bla'. rewrite kleisliVal. simpl.
  destruct H2 as [pv1 [pv2 [? [? ?]]]].
  rewrite <- (RUid d') in *.
  destruct (Unroll d') as [[i | f] | [pv1' pv2']]; apply RollInj in H2.
  inversion H2. inversion H7.
  inversion H2. inversion H7.
  rewrite -> URid.
  setoid_rewrite -> SUM_fun_simplx. destruct d as [a b]. simpl in *.
  have IH1' := IH1 _ _ H5; simpl in IH1'.
  have IH2' := IH2 _ _ H6; simpl in IH2'.
  -- assert (pv1 =-= pv1').
     apply tset_trans with (y:=pi1 (A:=DInf) (pv1,pv2)). auto.
     symmetry.
     apply tset_trans with (y:=pi1 (A:=DInf) (pv1',pv2')). auto.
     apply fmon_eq_compat. reflexivity. apply H2.
  -- assert (pv2 =-= pv2').
     apply tset_trans with (y:=pi2 (A:=DInf) (pv1,pv2)). auto.
     symmetry.
     apply tset_trans with (y:=pi2 (A:=DInf) (pv1',pv2')). auto.
     apply fmon_eq_compat. reflexivity. apply H2.
  rewrite <- H7, <- H8; clear H7 H8.
  rewrite -> IH1', -> IH2'.
  apply Smash_ValVal.
Qed.

Lemma rhoE_To_I_Eq_Pair (θ1 θ2 : LType) :
  rhoV_To_I_Eq θ1 ->
  rhoV_To_I_Eq θ2 ->
  rhoE_To_I_Eq θ1 ⨱ θ2.
Proof.
  intros θ1 θ2 IH1 IH2 p d H.
  apply Ole_antisym.
  apply rhoE_To_I_Leq_Pair. auto. auto. auto.
  apply rhoE_To_I_Geq_Pair. auto. auto. auto.
Qed.

Definition Def_Bracketing  (θ : LType) :=
 rhoV_E_In θ
 /\
 rhoV_To_I_Eq θ
 /\
 rhoE_E_In θ 
 /\
 rhoE_To_I_Eq θ
.

(** *Theorem 4.8: Bracketing *)
Theorem Bracketing : forall (θ : LType), Def_Bracketing θ.
Proof.
  induction θ.
  - Case "θ = bool".
    split.
    apply rhoV_E_In_Bool.
    split.
    apply rhoV_To_I_Eq_Bool.
    split.
    apply rhoE_E_In_Bool.
    apply rhoE_To_I_Eq_Bool.
  - Case "θ = nat".
    split.
    apply rhoV_E_In_Nat.
    split.
    apply rhoV_To_I_Eq_Nat.
    split.
    apply rhoE_E_In_Nat.
    apply rhoE_To_I_Eq_Nat.
  - Case "θ = θ1 ⇥ θ2".
    split.
    apply rhoV_E_In_Arr. apply IHθ2. apply IHθ1.
    split.
    apply rhoV_To_I_Eq_Arr. apply IHθ1. apply IHθ2.
    split.
    apply rhoE_E_In_Arr. apply IHθ2. apply IHθ1.
    apply rhoE_To_I_Eq_Arr. apply IHθ1. apply IHθ2.
  - Case "θ = θ1 ⨱ θ2".
    split.
    apply rhoV_E_In_Pair. apply IHθ1. apply IHθ2.
    split.
    apply rhoV_To_I_Eq_Pair. apply IHθ1. apply IHθ2.
    split.
    apply rhoE_E_In_Pair. apply IHθ1. apply IHθ2.
    apply rhoE_To_I_Eq_Pair. apply IHθ1. apply IHθ2.
Qed.

(** *Corollary 4 *)
Corollary EmbProjPair θ :
  forall (v : SemType θ), ↑⊥v =-= (↑θ) (↓θ v).
Proof.
  intros θ v; have B := Bracketing θ.
  destruct B as [? [? [? ?]]].
  unfold rhoV_E_In, rhoV_To_I_Eq in *.
  specialize (H0 _ _ (H v)).
  simpl in H0. rewrite -> URid in H0.
  auto.
Qed.

Definition rhoC (E : Env) (Γ : LCtx E) : SemCtx Γ -> SemEnv E -> Prop :=
  fun ξ η => forall (v : Var E), δ[lookupType Γ v] ((lookupV Γ v) ξ) (Roll (η !! v)).

Notation "'γ[' Γ ']'" := (@rhoC _ Γ) (at level 1, no associativity).

Definition RhoV (E : Env) (Γ : LCtx E) (θ : LType) :
  (SemCtx Γ =-> SemType θ) -> (SemEnv E =-> DInf) -> Prop :=
  fun td d => forall ξ η, γ[Γ] ξ η -> δ[θ] (td ξ) (d η).

Definition RhoE (E : Env) (Γ : LCtx E) (θ : LType) :
  (SemCtx Γ =-> SemType θ _BOT) -> (SemEnv E =-> DInf _BOT) -> Prop :=
  fun td d => forall ξ η, γ[Γ] ξ η -> ρ[θ] (td ξ) (d η).

(** *Notation *)
Notation "'Δ[' Γ , θ ']'" := (@RhoV _ Γ θ) (at level 1, no associativity).
Notation "'Ρ[' Γ , θ ']'" := (@RhoE _ Γ θ) (at level 1, no associativity).

Lemma PF_LET_unfolded : forall (θ1 θ2 : LType) (E : Env) (Γ : LCtx E)
                     (d1  : SemType θ1 _BOT)
                     (d2  : SemCtx (θ1 × Γ) =-> SemType θ2 _BOT)
                     (dv1 : DInf _BOT)
                     (dv2 : SemEnv E * VInf =-> DInf _BOT),
    ρ[θ1] d1 dv1 ->
    Ρ[θ1 × Γ, θ2] d2 dv2 ->
    forall ξ η,
      γ[Γ] ξ η ->
      ρ[θ2] ((kleisli d2) (((Smash (SemCtx Γ) (SemType θ1)) (Val ξ)) d1))
            ((KLEISLIR dv2) (η, KUR dv1)).
Proof.
  cofix PF_LET_unfolded.
  intros θ1 θ2 E Γ d1 d2 dv1 dv2 HI1 HI2. intros ξ η Hη.
  inversion HI1.
  - Case "SB".
    unfold KUR. do 2 rewrite kleisli_simpl. rewrite kleisli_Eps.
    rewrite KLEISLIR_Eps.
    rewrite Smash_Val. rewrite kleisli_simpl. do 2 rewrite kleisli_Eps.
    apply SB.
    simpl in PF_LET_unfolded. unfold id, KUR in PF_LET_unfolded.
    do 2 rewrite <- kleisli_simpl. rewrite <- Smash_Val.
    specialize (PF_LET_unfolded θ1 θ2 E Γ x d2 y dv2 H HI2 _ _ Hη).
    simpl in PF_LET_unfolded. unfold id in PF_LET_unfolded.
    rewrite <- kleisli_simpl.
    apply PF_LET_unfolded.
  - Case "SV".
    have ValExist := Val_exists_pred_eq (ex_intro _ n H).
    have ValExist' := Val_exists_pred_eq (ex_intro _ m H0).
    eapply (snd (delta_rho_compat θ2) _ _ _ _).
    rewrite <- ValExist. rewrite SmashLemmaValVal.
    2 : { split. apply tset_refl. apply tset_refl. }
    simpl. rewrite kleisliVal. apply tset_refl.
    rewrite <- ValExist'. unfold KUR. rewrite kleisliVal. simpl.
    rewrite KLEISLIR_unit2. apply tset_refl.
    assert (γ[θ1 × Γ] (ξ,d) (η,Unroll d')).
    intro v. dependent destruction v. simpl.
    eapply (fst (delta_rho_compat θ1) _ _ _ _). apply tset_refl.
    rewrite RUid. apply tset_refl. assumption. simpl. apply Hη.
    apply HI2. apply H4.
Qed.

Lemma PF_LET : forall (θ1 θ2 : LType) (E : Env) (Γ : LCtx E)
                 (d1 : SemCtx Γ =-> SemType θ1 _BOT)
                 (d2 : (SemCtx Γ * SemType θ1) =-> SemType θ2 _BOT)
                 (dv1 : SemEnv E =-> VInf _BOT)
                 (dv2 : (SemEnv E * VInf) =-> VInf _BOT),
    Ρ[Γ, θ1] d1 (KR << dv1) ->
    Ρ[θ1 × Γ, θ2] d2 (KR << dv2) ->
    Ρ[Γ, θ2] (LetTy d2 d1) (KR << LetApp dv2 dv1).
Proof.
  intros θ1 θ2 E Γ d1 d2 dv1 dv2 HI1 HI2. intros ξ η Hη.
  simpl. unfold id.
  specialize (HI1 _ _ Hη).
  have PF_LET_uf := (PF_LET_unfolded HI1 HI2 Hη). simpl in PF_LET_uf.
  eapply (snd (delta_rho_compat θ2) _ _ _ _). apply tset_refl.
  instantiate (1:=(KLEISLIR (KR << dv2)) (η, KUR (KR (dv1 η)))).
  rewrite KURKR_id. by rewrite <- KLEISLIR_KR_eq2.
  assumption.
Qed.

Lemma PF_IFB_unfolded : forall (θ : LType) (E : Env) (Γ : LCtx E)
                          (d0  : SemType bool̂ _BOT)
                          (d1 d2 : SemCtx Γ =-> SemType θ _BOT)
                          (dv0 : DInf _BOT)
                          (dv1 dv2 : SemEnv E =-> DInf _BOT),
    ρ[bool̂] d0 dv0 ->
    Ρ[Γ, θ] d1 dv1 ->
    Ρ[Γ, θ] d2 dv2 ->
    forall ξ η,
      γ[Γ] ξ η ->
      ρ[θ]
       ((kleisli ev)
          (((Smash (SemCtx Γ -=> SemType θ _BOT) (SemCtx Γ))
              ((kleisli (eta << DomainStuff.IfB (SemCtx Γ) (SemType θ _BOT)))
                 (((Smash
                      (prod_cpoType (SemCtx Γ -=> SemType θ _BOT)
                                    (SemCtx Γ -=> SemType θ _BOT)) 
                      (discrete_cpoType bool)) (Val (d1, d2))) 
                    d0))) (Val ξ)))
       (KR
          ((KLEISLIL
              (uncurry
                 (DomainStuff.IfZ (SemEnv E) (ExSem.VInf _BOT) <<
                    PAIR (discrete_cpoType nat) (KUR << dv2, KUR << dv1))))
             ((kleisli VInfToNat) (KUR dv0), η))).
Proof.
  cofix PF_IFB_unfolded.
  intros θ E Γ d0 d1 d2 dv0 dv1 dv2 HI0 HI1 HI2. intros ξ η Hη.
  inversion HI0.
  - Case "SB".
    rewrite Smash_Val. do 3 rewrite kleisli_simpl.
    do 2 rewrite kleisli_Eps. rewrite Smash_Eps_l. rewrite kleisli_Eps.
    unfold KUR. do 3 rewrite kleisli_simpl. do 2 rewrite kleisli_Eps.
    rewrite KLEISLIL_Eps. rewrite kleisli_Eps.
    repeat rewrite <- kleisli_simpl. apply SB.
    simpl in PF_IFB_unfolded. unfold KUR in PF_IFB_unfolded.
    rewrite <- Smash_Val. apply PF_IFB_unfolded. apply H. apply HI1. apply HI2.
    apply Hη.
  - Case "SV".
    have ValExist := Val_exists_pred_eq (ex_intro _ n H).
    have ValExist' := Val_exists_pred_eq (ex_intro _ m H0).
    eapply (snd (delta_rho_compat θ) _ _ _ _).
    rewrite <- ValExist. rewrite SmashLemmaValVal.
    2 : { split.
          rewrite SmashLemmaValVal.
          2 : { split. apply tset_refl. apply tset_refl. }
          rewrite kleisliVal. apply tset_refl. apply tset_refl.
    }
    rewrite kleisliVal. apply tset_refl.
    rewrite <- ValExist'. unfold KUR. rewrite kleisliVal. simpl.
    rewrite kleisliVal.
    simpl in H1. rewrite  -> H1. rewrite -> KLEISLIL_simpl. simpl.
    apply tset_refl.
    destruct d.
    + SCase "d = true".
      simpl.
      eapply (snd (delta_rho_compat θ) _ _ _ _). apply tset_refl.
      unfold KR. rewrite <- comp_simpl.
      rewrite <- kleisli_comp2.
      rewrite <- comp_assoc. rewrite RU_id. rewrite comp_idR.
      rewrite kleisli_unit. unfold Id; simpl; unfold id. apply tset_refl.
      apply HI1. assumption.
    + SCase "d = false".
      simpl.
      eapply (snd (delta_rho_compat θ) _ _ _ _). apply tset_refl.
      unfold KR. rewrite <- comp_simpl. rewrite <- kleisli_comp2.
      rewrite <- comp_assoc. rewrite RU_id. rewrite comp_idR.
      rewrite kleisli_unit. unfold Id; simpl; unfold id. apply tset_refl.
      apply HI2. assumption.
Qed.

Lemma PF_IFB : forall (θ : LType) (E : Env) (Γ : LCtx E)
                 (d0 : SemCtx Γ =-> SemType bool̂ _BOT)
                 (d1 d2 : SemCtx Γ =-> SemType θ _BOT)
                 (dv0 dv1 dv2 : SemEnv E =-> VInf _BOT),
    Ρ[Γ, bool̂] d0 (KR << dv0) ->
    Ρ[Γ, θ]   d1 (KR << dv1) ->
    Ρ[Γ, θ]   d2 (KR << dv2) ->
    Ρ[Γ, θ] (IfBTy d0 d1 d2) (KR << IfOneOp dv0 dv1 dv2).
Proof.
  intros θ E Γ d0 d1 d2 dv0 dv1 dv2 HI0 HI1 HI2.
  intros ξ η Hη. simpl. unfold id.
  specialize (HI0 _ _ Hη).
  have PF_IFB_uf := (PF_IFB_unfolded HI0 HI1 HI2 Hη). simpl in PF_IFB_uf.
  eapply (snd (delta_rho_compat θ) _ _ _ _). apply tset_refl.
  rewrite <- KURKR_id with (y:=dv0 η).
  unfold KR.
  assert (KLEISLIL
            (uncurry
               (DomainStuff.IfZ (SemEnv E) (ExSem.VInf _BOT) <<
                                PAIR (discrete_cpoType nat)
                                (KUR << (KR << dv2), KUR << (KR << dv1))))
            =-=
            KLEISLIL
            (uncurry
               (DomainStuff.IfZ (SemEnv E) (ExSem.VInf _BOT) <<
                                PAIR (discrete_cpoType nat)
                                (dv2,dv1)))
         ). apply KLEISLIL_eq_compat.
  apply fmon_eq_intro. intro η'. destruct η'. simpl.
  destruct s. simpl. apply KURKR_id.
  simpl. apply KURKR_id.
  rewrite <- H. clear H. apply tset_refl.
  apply PF_IFB_uf.
Qed.

Lemma PF_APP : forall (θ1 θ2 : LType) (E : Env) (Γ : LCtx E)
                 (f : SemCtx Γ =-> SemType θ1 ⇥ θ2)
                 (a : SemCtx Γ =-> SemType θ1)
                 (fv av : SemEnv E =-> VInf),
    Δ[Γ, θ1 ⇥ θ2] f (Roll << fv) ->
    Δ[Γ, θ1]       a (Roll << av) ->
    Ρ[Γ, θ2] (AppTy f a) (KR << AppOp fv av).
Proof.
  intros θ1 θ2 E Γ f a fv av HIf HIa. intros ξ η Hη.
  specialize (HIf _ _ Hη). specialize (HIa _ _ Hη). simpl.
  destruct HIf as [gv [? ?]].
  simpl in H. apply RollInj in H.
  specialize (H0 _ _ HIa).
  eapply (snd (delta_rho_compat θ2) _ _ _ _). apply tset_refl.
  rewrite H. do 2 rewrite SUM_fun_simplx. rewrite KLEISLIL_unit2.
  unfold KR. rewrite <- comp_simpl. rewrite <- kleisli_comp2.
  rewrite <- comp_assoc. rewrite RU_id. rewrite comp_idR.
  rewrite -> kleisli_unit. unfold Id; simpl; unfold id. apply tset_refl.
  assumption.
Qed.

Lemma PF_FUN : forall (θ1 θ2 : LType) (E : Env) (Γ : LCtx E)
                 (d : SemCtx (θ1 × (θ1 ⇥ θ2) × Γ) =-> SemType θ2 _BOT)
                 (dv : SemEnv E.+2 =-> VInf _BOT),
    Ρ[θ1 × (θ1 ⇥ θ2) × Γ, θ2] d (KR << dv) ->
    forall ξ η, γ[Γ] ξ η ->
            δ[θ1 ⇥ θ2] (fixp (exp_fun d << PAIR (SemType θ1 ⇥ θ2) ξ))
                        (Roll (inFun (fixp ((F dv) η)))).
Proof.
  intros θ1 θ2 E Γ d dv H ξ η Hη.
  eapply (fst (delta_rho_compat θ1 ⇥ θ2) _ _ _ _). apply tset_refl.
  do 2 rewrite lub_comp_eq. apply tset_refl.
  apply (fst (delta_rho_cc θ1 ⇥ θ2)).
  induction i. simpl. eexists. split. apply tset_refl.
  intros x y H0. simpl. apply rho_strict.
  simpl. eexists. split. apply tset_refl.
  intros x y Hxy. simpl. unfold id.
  assert (γ[θ1 × (θ1 ⇥ θ2) × Γ]
           ( ξ
           , iter_ (exp_fun d << PAIR (SemType θ1 -=> SemType θ2 _BOT) ξ)i
           , x)
           ( η
           , inFun (iter_
                      (exp_fun
                         ((kleisli (eta << ExSem.Roll) << dv)
                            <<
                          (Id >< inFun) >< ExSem.Unroll) <<
                         PAIR (ExSem.DInf -=> ExSem.DInf _BOT) η) i)
           , ExSem.Unroll y
           )
         ).
    intro v. dependent destruction v.
    + SCase "v = ZVAR".
      simpl. eapply (fst (delta_rho_compat θ1) _ _ _ _). apply tset_refl.
        by rewrite RUid. assumption.
    dependent destruction v.
    + SCase "v = SVAR ZVAR". apply IHi.
    + SCase "v = SVAR SVAR". apply Hη.
    specialize (H _ _ H0).
    apply H.
Qed.

Lemma PF_FST : forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
                 (d : SemCtx Γ =-> SemType θ ⨱ θ')
                 (dv : SemEnv E =-> VInf),
    Δ[Γ, θ ⨱ θ']   d (Roll << dv) ->
    Ρ[Γ, θ] (FstTy d) (KR << FSTOp dv).
Proof.
  intros θ θ' E Γ d dv IH.
  intros ξ η Hη. simpl.
  specialize (IH _ _ Hη). destruct IH as [pv1 [pv2 [? [? ?]]]].
  simpl in H. apply RollInj in H.
  eapply (snd (delta_rho_compat θ)). reflexivity.
  rewrite -> H. setoid_rewrite -> SUM_fun_simplx. unfold KR; simpl.
  rewrite -> kleisliVal. simpl. rewrite -> kleisliVal. simpl.
  apply Val_eq_compat. rewrite -> RUid. reflexivity.
  apply SV with (m:=0) (d:=fst (d ξ)) (n:=0) (d':=pv1). auto. auto.
  apply H0.
Qed.

Lemma PF_SND : forall (θ θ' : LType) (E : Env) (Γ : LCtx E)
                 (d : SemCtx Γ =-> SemType θ ⨱ θ')
                 (dv : SemEnv E =-> VInf),
    Δ[Γ, θ ⨱ θ']   d (Roll << dv) ->
    Ρ[Γ, θ'] (SndTy d) (KR << SNDOp dv).
Proof.
  intros θ θ' E Γ d dv IH.
  intros ξ η Hη. simpl.
  specialize (IH _ _ Hη). destruct IH as [pv1 [pv2 [? [? ?]]]].
  simpl in H. apply RollInj in H.
  eapply (snd (delta_rho_compat θ')). reflexivity.
  rewrite -> H. setoid_rewrite -> SUM_fun_simplx. unfold KR; simpl.
  rewrite -> kleisliVal. simpl. rewrite -> kleisliVal. simpl.
  apply Val_eq_compat. rewrite -> RUid. reflexivity.
  apply SV with (m:=0) (d:=snd (d ξ)) (n:=0) (d':=pv2). auto. auto.
  apply H1.
Qed.

Lemma PF_subs_delta : forall (θ θ' : LType) (x : SemType θ) (y : DInf)
                        (tjs : (θ t≤ θ')),
    δ[θ] x y -> δ[θ'] (SemTypeJudgeL tjs x) y.
Proof.
  intros θ θ' x y tjs H.
  generalize dependent y.
  dependent induction tjs.
  - Case "bool ≤ nat".
    intros y H. simpl in *. by rewrite -> H.
  - Case "θ ≤ θ".
    intros y H. simpl in *. by unfold id.
  - Case "θ ≤ θ' ∧ θ' ≤ θ''".
    intros y H. simpl. apply IHtjs2. apply IHtjs1. apply H.
  - Case "(θ0,θ1) ≤ (θ0',θ1')".
    intros y H. simpl in *. destruct H as [pv1 [pv2 [? [? ?]]]].
    exists pv1, pv2. split. auto. split. apply IHtjs1. auto. apply IHtjs2. auto.
  - Case "θ0 ⇥ θ1 x y ≤ θ0' ⇥ θ1'".
    intros y H. simpl.
    destruct H as [f [? ?]].
    exists f. split. auto. intros x0 y0 H1. unfold id.
    specialize (IHtjs1 _ _ H1).
    specialize (H0 _ _ IHtjs1).
    assert ( forall a b, SE δ[ θ1] a b ->
                    SE δ[ θ1'] ((kleisli (eta << t⟦ tjs2 ⟧l)) a) b).
    cofix PF_subs_delta. intros a b H2.
    inversion H2.
    rewrite kleisli_simpl. rewrite kleisli_Eps.
    apply SB. rewrite <- kleisli_simpl. apply PF_subs_delta.
    auto.
    have ValExist := Val_exists_pred_eq (ex_intro _ n H3).
    have ValExist' := Val_exists_pred_eq (ex_intro _ m H4).
    eapply (snd (delta_rho_compat θ1') _ _ _ _).
    rewrite <- ValExist. rewrite -> kleisliVal. by simpl. by rewrite <- ValExist'.
    apply SV with (m:=0) (d:=t⟦ tjs2 ⟧l d) (n:=0) (d':=d'). auto. auto.
    apply IHtjs2. auto.
    apply H2. auto.
Qed.

Lemma PF_subs_Delta : forall (E : Env) (Γ : LCtx E) (θ θ' : LType)
                        (f : SemCtx Γ =-> SemType θ)
                        (g : SemEnv E =-> DInf)
                        (tjs : (θ t≤ θ')),
    Δ[Γ,θ] f g -> Δ[Γ,θ'] (SemTypeJudgeL tjs << f) g.
Proof.
  intros E Γ θ θ' f g tjs H ξ η Hη.
  simpl. apply PF_subs_delta. auto.
Qed.

Lemma PF_subs_rho : forall (θ θ' : LType) (x : SemType θ _BOT) (y : DInf _BOT)
                      (tjs : (θ t≤ θ')),
    ρ[θ] x y -> ρ[θ'] (kleisli (eta << SemTypeJudgeL tjs) x) y.
Proof.
  cofix PF_subs_rho.
  intros θ θ' x y tjs IH.
  inversion IH.
  - Case "SB".
    rewrite kleisli_simpl. rewrite kleisli_Eps.
    apply SB. rewrite <- kleisli_simpl. apply PF_subs_rho. auto.
  - Case "SV".
    have ValExist := Val_exists_pred_eq (ex_intro _ n H).
    have ValExist' := Val_exists_pred_eq (ex_intro _ m H0).
    eapply (snd (delta_rho_compat θ') _ _ _ _).
    rewrite <- ValExist. rewrite -> kleisliVal. by simpl. by rewrite <- ValExist'.
    apply SV with (m:=0) (d:=t⟦ tjs ⟧l d) (n:=0) (d':=d'). auto. auto.
    apply PF_subs_delta. auto.
Qed.

Lemma PF_subs_Rho : forall (E : Env) (Γ : LCtx E) (θ θ' : LType)
                        (f : SemCtx Γ =-> SemType θ _BOT)
                        (g : SemEnv E =-> DInf _BOT)
                        (tjs : (θ t≤ θ')),
    Ρ[Γ,θ] f g -> Ρ[Γ,θ'] (kleisli (eta << SemTypeJudgeL tjs) << f) g.
Proof.
  intros E Γ θ θ' f g tjs H ξ η Hη.
  simpl. apply PF_subs_rho. auto.
Qed.

Theorem EPPair_SemSubType :
  forall (θ θ' : LType) (x : SemType θ) (y : SemType θ') (tjs : (θ t≤ θ')),
    (↑θ') (↓θ x) =-= eta y -> SemTypeJudgeL tjs x =-= y.
Proof.
  intros θ θ' x y tjs H.
  have B := Bracketing θ.
  have B' := Bracketing θ'.
  destruct B as [? _].
  destruct B' as [_ [? _]].
  specialize (H0 x).
  apply PF_subs_delta with (θ':=θ') (tjs:=tjs) in H0.
  specialize (H1 _ _ H0). simpl in H1. rewrite -> URid in H1.
  rewrite -> H in H1. apply vinj in H1. auto.
Qed.

(** *Theorem 11: Fundamental theorem of Logical Relations *)
Lemma PF : forall (E : Env),
    (forall (v : V E) (Γ : LCtx E) (θ : LType)
       (tj : (Γ v⊢ v ⦂ θ)),
        Δ[Γ,θ] t⟦ tj ⟧v (Roll << ⟦ v ⟧v)
    )
        /\
    (forall (e : Expr E) (Γ : LCtx E) (θ : LType)
       (tj : (Γ e⊢ e ⦂ θ)),
        Ρ[Γ,θ] t⟦ tj ⟧e (KR << ⟦ e ⟧e)
    )
.
Proof.
  apply mutual_VE_induction.
  - Case "VAR".
    intros E v Γ θ tj ξ η H. dependent induction tj. simpl. apply H.
    apply PF_subs_delta. apply IHtj. auto. auto. auto.
  - Case "BOOL".
    intros E v Γ θ tj ξ η H. dependent induction tj.
    simpl. rewrite URid. by do 2 setoid_rewrite SUM_fun_simplx.
    apply PF_subs_delta. apply IHtj. auto. auto. auto.
  - Case "NAT".
    intros E v Γ θ tj ξ η H. dependent induction tj.
    simpl. rewrite URid. by do 2 setoid_rewrite SUM_fun_simplx.
    apply PF_subs_delta. apply IHtj. auto. auto. auto.
  - Case "FUN".
    intros E e H Γ θ tj. dependent induction tj. intros ξ η Hη.
    eapply (fst (delta_rho_compat θ' ⇥ θ) _ _ _ _). rewrite FunRule_simpl.
    apply tset_refl. rewrite comp_simpl. rewrite -> SemVal_FUN_equation2.
    apply tset_refl. apply PF_FUN. apply H. apply Hη.
    apply PF_subs_Delta. apply IHtj. auto. auto. auto.
  - Case "PAIR".
    intros E e H e' H' Γ θ tj. dependent induction tj. intros ξ η Hη.
    simpl in *; unfold id.
    exists (Roll (⟦ e ⟧v η)), (Roll (⟦ e' ⟧v η)). split. auto.
    split.
    specialize (H Γ θ tj1 ξ η Hη). apply H.
    specialize (H' Γ θ' tj2 ξ η Hη). apply H'.
    apply PF_subs_Delta. apply IHtj. auto. auto. auto. auto.
  - Case "VAL".
    intros E v HI Γ θ tj ξ η H. dependent induction tj. simpl.
    unfold KR. rewrite kleisli_simpl; rewrite kleisli_Val. simpl.
    apply SV with (n:=0) (d':=Roll (⟦v ⟧v η)) (m:=0) (d:=t⟦t ⟧v ξ).
    apply pred_nth_val. apply pred_nth_val.
    apply HI. assumption.
    apply PF_subs_rho. apply IHtj. auto. auto. auto. auto.
  - Case "APP".
    intros E f HIf a HIa Γ θ tj. intros ξ η Hη.
    dependent induction tj. apply PF_APP. apply HIf. apply HIa. apply Hη.
    apply PF_subs_rho. apply IHtj. auto. auto. auto. auto. auto.
  - Case "OrdOp".
    intros E n e H e0 H0 Γ θ tj. intros ξ η Hη.
    dependent induction tj. simpl. unfold KR.
    specialize (H _ _ tj1 _ _ Hη).
    specialize (H0 _ _ tj2 _ _ Hη).
    have bla := rhoOrdOp (SemOrdOp n) H H0. simpl in bla. unfold id in *.
    eapply (snd (delta_rho_compat bool̂)) in bla.
    2 : { apply tset_refl. }
    2 : { do 2 rewrite KURKR_id. apply tset_refl. }
    apply bla.
    apply PF_subs_rho. apply IHtj. auto. auto. auto. auto. auto.
  - Case "BoolOp".
    intros E n e H e0 H0 Γ θ tj. intros ξ η Hη.
    dependent induction tj. simpl. unfold KR.
    specialize (H _ _ tj1 _ _ Hη).
    specialize (H0 _ _ tj2 _ _ Hη).
    have bla := rhoBoolOp (SemBoolOp n) H H0. simpl in bla. unfold id in *.
    eapply (snd (delta_rho_compat bool̂)) in bla.
    2 : { apply tset_refl. } 
    2 : { do 2 rewrite KURKR_id. apply tset_refl. }
    apply bla.
    apply PF_subs_rho. apply IHtj. auto. auto. auto. auto. auto.
  - Case "NatOp".
    intros E n e H e0 H0 Γ θ tj. intros ξ η Hη.
    dependent induction tj. simpl. unfold KR.
    specialize (H _ _ tj1 _ _ Hη).
    specialize (H0 _ _ tj2 _ _ Hη).
    have bla := rhoNatOp (SemNatOp n) H H0. simpl in bla. unfold id in *.
    eapply (snd (delta_rho_compat nat̂)) in bla.
    2 : { apply tset_refl. } 
    2 : { do 2 rewrite KURKR_id. apply tset_refl. }
    apply bla.
    apply PF_subs_rho. apply IHtj. auto. auto. auto. auto. auto.
  - Case "LET".
    intros E e HIe e' HIe' Γ θ tj.
    dependent induction tj. apply PF_LET. apply HIe. apply HIe'.
    intros ξ η Hη. apply PF_subs_rho. apply IHtj. auto. auto. auto. auto. auto.
  - Case "IFZ".
    intros E e0 HI0 e1 HI1 e2 HI2 Γ θ tj.
    dependent induction tj. apply PF_IFB.  apply HI0. apply HI1. apply HI2.
    intros ξ η Hη. apply PF_subs_rho.
    apply IHtj. auto. auto. auto. auto. auto. auto.
  - Case "FST".
    intros E v IH Γ θ tj.
    dependent induction tj. apply PF_FST. apply IH.
    intros ξ η Hη. apply PF_subs_rho. apply IHtj. auto. auto. auto. auto.
  - Case "SND".
    intros E v IH Γ θ tj.
    dependent induction tj. apply PF_SND. apply IH.
    intros ξ η Hη. apply PF_subs_rho. apply IHtj. auto. auto. auto. auto.
Qed.

Lemma Gamma_E_In : forall (E : Env) (Γ : LCtx E) (ξ : SemCtx Γ),
    γ[Γ] ξ (⇓ Γ ξ).
Proof.
  intros E Γ ξ v.
  dependent induction v.
  dependent destruction Γ.
  simpl. apply Bracketing.
  dependent destruction Γ.
  simpl. apply IHv.
Qed.

(** *Theorem 12 *)
Theorem In_eq_Ex : forall (E : Env) (Γ : LCtx E) (θ : LType)
                     (ξ : SemCtx Γ) (e : Expr E) (tj : (Γ e⊢ e ⦂ θ)),
    kleisli (↑ θ) (⟦ e ⟧e (⇓ Γ ξ)) =-= t⟦ tj ⟧e ξ.
Proof.
  intros E Γ θ ξ e tj.
  have PF := snd (PF E) e Γ θ tj ξ ((GtoE Γ) ξ) (@Gamma_E_In E Γ ξ).
  have Bracketing := snd (snd (snd (Bracketing θ))).
  specialize (Bracketing _ _ PF). simpl in Bracketing.
  rewrite <- Bracketing. unfold KR. simpl. unfold id.
  rewrite <- comp_simpl with (g:=(kleisli (eta << DomainStuff.Roll))).
  rewrite <- kleisli_comp2.
  rewrite <- comp_assoc. rewrite UR_id. rewrite comp_idR.
  reflexivity.
Qed.

Theorem In_eqV_Ex : forall (E : Env) (Γ : LCtx E) (θ : LType)
                      (ξ : SemCtx Γ) (v : V E) (tj : (Γ v⊢ v ⦂ θ)),
    kleisli (↑ θ) (eta (⟦ v ⟧v (⇓ Γ ξ))) =-= eta (t⟦ tj ⟧v ξ).
Proof.
  intros E Γ θ ξ e tj.
  rewrite <- ValRule_simpl.
  rewrite <- SemExp_VAL_equation.
  apply In_eq_Ex.
Qed.

Lemma KRInjLe : forall (d d' : VInf _BOT),
    (kleisli (eta << Roll)) d <= (kleisli (eta << Roll)) d'
    ->
    d <= d'.
Proof.
  cofix KRInjLe.
  intros d d' H. destruct d. destruct d'.
  inversion H. apply DLleEps. apply KRInjLe.
  rewrite kleisli_simpl in H0. rewrite kleisli_Eps in H0.
  rewrite <- kleisli_simpl in H0.
  rewrite kleisli_simpl in H1. rewrite kleisli_Eps in H1.
  rewrite <- kleisli_simpl in H1.
  inversion H0. inversion H1. rewrite <- H4. rewrite <- H5. apply H2.
  rewrite kleisli_simpl in H1. rewrite kleisli_Eps in H1. inversion H1.
  rewrite kleisli_simpl in H0. rewrite kleisli_Eps in H0. inversion H0.
  apply DLleEpsVal. apply KRInjLe.
  rewrite kleisli_simpl in H. rewrite kleisli_Eps in H.
  rewrite <- kleisli_simpl in H.
  inversion H.
  rewrite kleisli_simpl in H1. rewrite kleisli_Val in H1. inversion H1.
  rewrite kleisli_simpl in H1. rewrite kleisli_Val in H1.
  rewrite H1 in H2. rewrite kleisliVal.
  apply H2.
  inversion H.
  rewrite kleisli_simpl in H0. rewrite kleisli_Val in H0. inversion H0.
  rewrite kleisli_simpl in H0. rewrite kleisli_Val in H0. inversion H0.
  have ValExist := Val_exists_pred_eq (ex_intro _ n H1).
  apply tset_sym in ValExist.
  have blaaa := kleisliValVal ValExist.
  destruct blaaa as [? [? ?]]. rewrite -> H4.
  apply Val_le_compat.
  simpl in *.
  apply vinj with (D:=DInf) in H5.
  rewrite <- H5 in H2.
  rewrite kleisli_simpl in H0. rewrite kleisli_Val in H0. simpl in H0.
  inversion H0. rewrite -> H7 in H2.
  apply RollInjle in H2.
  assumption.
Qed.
 
Lemma KRInj : forall (d d' : VInf _BOT),
    (kleisli (eta << Roll)) d =-= (kleisli (eta << Roll)) d'
    ->
    d =-= d'.
Proof.
  split. apply KRInjLe. apply H.
  apply KRInjLe. apply H.
Qed.

Lemma deltaBoolFunc : RelFunc δ[bool̂].
Proof.
  intros x y z H H0.
  simpl in *.
  rewrite <- RUid with (x:=y). rewrite <- RUid with (x:=z).
  destruct (Unroll y) as [[n | f] | p].
  destruct (Unroll z) as [[n' | f'] | p'].
  do 2 setoid_rewrite -> SUM_fun_simplx in H.
  do 2 setoid_rewrite -> SUM_fun_simplx in H0.
  apply monotonic_stable. auto.
  apply vinj with (D:=nat_cpoType) in H.
  apply vinj with (D:=nat_cpoType) in H0.
  rewrite <- H0 in H. auto.
  do 2 setoid_rewrite -> SUM_fun_simplx in H0. simpl in H0.
  apply tset_sym in H0. apply PBot_incon_eq in H0. contradiction.
  setoid_rewrite -> SUM_fun_simplx in H0. simpl in H0.
  apply tset_sym in H0. apply PBot_incon_eq in H0. contradiction.
  do 2 setoid_rewrite -> SUM_fun_simplx in H. simpl in H.
  apply tset_sym in H. apply PBot_incon_eq in H. contradiction.
  setoid_rewrite -> SUM_fun_simplx in H. simpl in H.
  apply tset_sym in H. apply PBot_incon_eq in H. contradiction.
Qed.

Lemma deltaNatFunc : RelFunc δ[nat̂].
Proof.
  intros x y z H H0.
  simpl in *.
  rewrite <- RUid with (x:=y). rewrite <- RUid with (x:=z).
  destruct (Unroll y) as [[n | f] | p].
  destruct (Unroll z) as [[n' | f'] | p'].
  do 2 setoid_rewrite -> SUM_fun_simplx in H.
  do 2 setoid_rewrite -> SUM_fun_simplx in H0.
  apply monotonic_stable. auto.
  apply vinj with (D:=nat_cpoType) in H.
  apply vinj with (D:=nat_cpoType) in H0.
  rewrite <- H0 in H. auto.
  do 2 setoid_rewrite -> SUM_fun_simplx in H0. simpl in H0.
  apply tset_sym in H0. apply PBot_incon_eq in H0. contradiction.
  setoid_rewrite -> SUM_fun_simplx in H0. simpl in H0.
  apply tset_sym in H0. apply PBot_incon_eq in H0. contradiction.
  do 2 setoid_rewrite -> SUM_fun_simplx in H. simpl in H.
  apply tset_sym in H. apply PBot_incon_eq in H. contradiction.
  setoid_rewrite -> SUM_fun_simplx in H. simpl in H.
  apply tset_sym in H. apply PBot_incon_eq in H. contradiction.
Qed.

Lemma rhoNatFunc : forall (x : SemType nat̂) (y z : DInf _BOT),
    ρ[nat̂] (Val x) y -> ρ[nat̂] (Val x) z -> y =-= z.
Proof.
  apply (SEFuncVal deltaNatFunc).
Qed.

Theorem Ex_eq_In : forall (ξ : SemCtx []) (e : Expr 0) (tj : ([] e⊢ e ⦂ nat̂)),
    ⟦ e ⟧e (⇓ [] ξ) =-= kleisli (eta << ↓ nat̂) (t⟦ tj ⟧e ξ).
Proof.
  intros ξ e tj.
  have PF := snd (PF 0) e [] nat̂ tj ξ ((⇓ []) ξ) (@Gamma_E_In 0 [] ξ).
  have Bracketing := fst (snd (snd (Bracketing nat̂))).
  specialize (Bracketing (t⟦tj ⟧e ξ)). simpl in *. unfold id, KR in *.
  have SEF := SEFunc deltaNatCompat deltaNatFunc PF Bracketing.
  apply tset_sym in SEF. rewrite -> kleisli_comp2 in SEF.
  simpl in SEF. apply KRInj in SEF.
    by rewrite SEF.
Qed.

Theorem Ex_eq_In_b : forall (ξ : SemCtx []) (e : Expr 0) (tj : ([] e⊢ e ⦂ bool̂)),
    ⟦ e ⟧e (⇓ [] ξ) =-= kleisli (eta << ↓ bool̂) (t⟦ tj ⟧e ξ).
Proof.
  intros ξ e tj.
  have PF := snd (PF 0) e [] bool̂ tj ξ ((⇓ []) ξ) (@Gamma_E_In 0 [] ξ).
  have Bracketing := fst (snd (snd (Bracketing bool̂))).
  specialize (Bracketing (t⟦tj ⟧e ξ)). simpl in *. unfold id, KR in *.
  have SEF := SEFunc deltaBoolCompat deltaBoolFunc PF Bracketing.
  apply tset_sym in SEF. rewrite -> kleisli_comp2 in SEF.
  simpl in SEF. apply KRInj in SEF.
    by rewrite SEF.
Qed.

Theorem Ex_eqV_In : forall (ξ : SemCtx []) (v : V 0) (tj : ([] v⊢ v ⦂ nat̂)),
    ⟦ v ⟧v (⇓ [] ξ) =-= ↓ nat̂ (t⟦ tj ⟧v ξ).
Proof.
  intros ξ v tj.
  have PF := fst (PF 0) v [] nat̂ tj ξ ((⇓ []) ξ) (@Gamma_E_In 0 [] ξ).
  simpl in *. apply VInfToNat_prop in PF. rewrite -> URid in PF.
    by rewrite -> PF.
Qed.

(** *Corollary 5: Coherence *)
Theorem Coherence :  forall (E : Env) (Γ : LCtx E) (θ : LType)
                       (ξ : SemCtx Γ) (e : Expr E) (tj tj' : (Γ e⊢ e ⦂ θ)),
    t⟦ tj ⟧e ξ =-= t⟦ tj' ⟧e ξ.
Proof.
  intros E Γ θ ξ e tj tj'.
  have eq := In_eq_Ex ξ tj.
  have eq' := In_eq_Ex ξ tj'.
    by rewrite <- eq, eq'.
Qed.
