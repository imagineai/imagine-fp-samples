(**********************************************************************************
 * typedsubst.v                                                                   *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * July 2010                                                                      *
 * Build with Coq 8.2pl1 plus SSREFLECT                                           *
 **********************************************************************************)

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

Require Import PredomAll.
Require Import typedlambda.
Require Import typeddensem.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* Need this for nice pretty-printing *)
Unset Printing Implicit Defensive.

(*==========================================================================
  Semantics of substitution and renaming
  ==========================================================================*)

(* Apply semantic function pointwise to a renaming or substitution *)
(*=SemSub *)
Fixpoint SemSub E E' : Sub E' E -> SemEnv E =-> SemEnv E' := 
  match E' return Sub E' E -> SemEnv E =-> SemEnv E' with
  | nil => fun s => terminal_morph (SemEnv E)
  | _ :: _ => fun s => <| SemSub (tlMap s) , SemVal (hdMap s) |>
  end.
(*=End *)

Fixpoint SemRen E E' : Ren E' E -> SemEnv E =-> SemEnv E' := 
  match E' with
| nil => fun s => terminal_morph (SemEnv E)
| _ :: _ => fun s => <| SemRen (tlMap s) , SemVar (hdMap s) |>
  end.

Lemma SemLiftRen : 
  forall E E' (r : Ren E E') ty, SemRen (tlMap (liftRen ty r)) =-= SemRen r << pi1.
Proof.
elim.
- move => E' r ty.
  by apply: terminal_unique.
- move => t s IH E' r ty.
  simpl. destruct (consMapInv r) as [r' [var eq]]. 
  subst. simpl. rewrite hdConsMap. rewrite tlConsMap.
  specialize (IH E' r' ty). apply: prod_unique.
  + rewrite prod_fun_fst. rewrite comp_assoc. by rewrite prod_fun_fst.
  + rewrite prod_fun_snd. rewrite comp_assoc. by rewrite prod_fun_snd.
Qed.

Lemma SemLift2Ren : 
  forall E E' (r : Ren E E') ty ty', SemRen (tlMap (tlMap (liftRen ty' (liftRen ty r)))) =-= SemRen r << pi1 << pi1. 
Proof.
elim.
- move => E' r ty ty'. by apply: terminal_unique.
- move => t s IH E' r ty ty'. simpl. destruct (consMapInv r) as [r' [var eq]].
  subst. simpl. rewrite hdConsMap. rewrite tlConsMap.
  specialize (IH E' r' ty). apply: prod_unique.
  + rewrite prod_fun_fst. rewrite comp_assoc. rewrite comp_assoc. rewrite prod_fun_fst. by apply IH.
  + rewrite prod_fun_snd. do 2 rewrite comp_assoc. by rewrite prod_fun_snd.
Qed.

(*==========================================================================
  Semantic function commutes with renaming
  ==========================================================================*)

Lemma SemCommutesWithRen E:
   (forall t (v : Value E t) E' (r : Ren E E'),
   SemVal v << SemRen r =-= SemVal (renameVal r v))
/\ (forall t (exp : Exp E t) E' (r : Ren E E'),
   SemExp exp << SemRen r =-= SemExp (renameExp r exp)).
Proof.
apply ExpVal_ind.

(* TINT *)
intros. simpl. rewrite <- const_com; trivial.

(* TBOOL *)
intros. simpl. rewrite <- const_com; trivial.

(* TVAR *)
intros E ty var E' r.
simpl. 
induction var. 
simpl. rewrite prod_fun_snd.
destruct (consMapInv r) as [r' [v eq]]. subst.
simpl. rewrite hdConsMap. trivial.
destruct (consMapInv r) as [r' [v eq]]. subst.
simpl. 
specialize (IHvar r').
rewrite <- IHvar. rewrite <- comp_assoc.
rewrite tlConsMap. by rewrite prod_fun_fst.

(* TFIX *)
intros E t t1 body IH E' s. 
specialize (IH _ (liftRen _ (liftRen _ s))).
rewrite renameTFIX.
simpl SemVal. rewrite <- comp_assoc.
do 2 rewrite exp_comp. rewrite <- IH. simpl. rewrite SemLift2Ren.
rewrite prod_fun_compl. rewrite comp_idL. by rewrite comp_idL.

(* TPAIR *)
intros E t1 t2 v1 IH1 v2 IH2 E' s.
rewrite renameTPAIR. simpl SemVal. rewrite <- IH1. rewrite <- IH2. by rewrite <- prod_fun_compl.

(* TFST *)
intros E t1 t2 v IH E' s. rewrite renameTFST. simpl. 
rewrite <- IH. by repeat (rewrite comp_assoc).

(* TSND *)
intros E t1 t2 v IH E' s. rewrite renameTSND. simpl. 
rewrite <- IH. by repeat (rewrite comp_assoc).

(* TOP *)
intros E n v1 IH1 v2 IH2 E' s. rewrite renameTOP. simpl.
repeat (rewrite <- comp_assoc). rewrite <- IH1. rewrite <- IH2.
by rewrite prod_fun_compl. 

(* TGT *)
intros E v1 IH1 v2 IH2 E' s. rewrite renameTGT. simpl. 
repeat (rewrite <- comp_assoc). rewrite <- IH1. rewrite <- IH2.
by rewrite prod_fun_compl.

(* TVAL *)
intros E t v IH E' s. rewrite renameTVAL. simpl.
rewrite <- IH. by rewrite <- comp_assoc.

(* TLET *)
intros E t1 t2 e2 IH2 e1 IH1 E' s. rewrite renameTLET. simpl. 
rewrite <- comp_assoc.
specialize (IH2 _ s).
specialize (IH1 _ (liftRen _ s)).
rewrite prod_fun_compl.
rewrite KLEISLIR_comp.
rewrite <- IH2. clear IH2. rewrite <- IH1. clear IH1. simpl.
do 2 rewrite comp_idL. by rewrite SemLiftRen.

(* TAPP *)
intros E t1 t2 v1 IH1 v2 IH2 E' s. rewrite renameTAPP. simpl. 
rewrite <- comp_assoc. rewrite <- IH1. rewrite <- IH2.
by rewrite prod_fun_compl.

(* TIF *)
intros E t ec IHc te1 IH1 te2 IH2 E' s. rewrite renameTIF. simpl.
rewrite choose_comp. rewrite -> IH1. rewrite -> IH2. by rewrite -> IHc.
Qed.

Set Printing Implicit Defensive.

Lemma SemShiftRen : 
  forall E E' (r : Ren E E') ty, SemRen (shiftRen ty r) =-= SemRen r << pi1.
Proof.
elim.
- move => E' r ty. simpl. by apply: terminal_unique.
- move => t E IH E' r ty. simpl.
  case: (consMapInv r) => r' ; case => var eq.
  rewrite -> eq. clear r eq. simpl. rewrite hdConsMap. rewrite tlConsMap. 
  specialize (IH E' r' ty). rewrite IH.
  by rewrite prod_fun_compl.
Qed.

Lemma SemIdRen : forall E, SemRen (idRen E) =-= Id.
elim.
- simpl. by apply: terminal_unique.
- move => t E IH. simpl. rewrite idRenDef. rewrite tlConsMap.
  rewrite SemShiftRen. rewrite IH. rewrite comp_idL.
  by apply: prod_unique ; [rewrite prod_fun_fst | rewrite prod_fun_snd] ; rewrite comp_idR.
Qed.


Lemma SemShiftSub : 
  forall E E' (s : Sub E E') ty, SemSub (shiftSub ty s) =-= SemSub s << pi1.
elim.
- move => E' s ty. simpl. by apply: terminal_unique.
- move => t E IH E' s ty. simpl.
  case: (consMapInv s) => s' ; case => var eq. rewrite eq ; clear s eq.
  rewrite hdConsMap. rewrite tlConsMap. specialize (IH E' s' ty).
  rewrite prod_fun_compl. rewrite IH. unfold shiftSub. rewrite shiftConsMap.
  rewrite hdConsMap. simpl. rewrite <- (proj1 (SemCommutesWithRen _)).
(* Seems a bit round-about *)
have e: ((fun t0 => SVAR ty) = tlMap (liftRen ty (idRen E'))).
rewrite LiftRenDef. rewrite tlConsMap. by apply MapExtensional.
rewrite e.
rewrite SemLiftRen. rewrite SemIdRen. by rewrite comp_idL.
Qed.


Lemma SemLiftSub : 
  forall E E' (s : Sub E E') ty, SemSub (tlMap (liftSub ty s)) =-= SemSub s << pi1.
Proof.
intros.
rewrite LiftSubDef. rewrite tlConsMap. apply SemShiftSub. 
Qed.

Lemma SemLift2Sub : 
  forall E E' (s : Sub E E') ty ty', SemSub (tlMap (tlMap (liftSub ty' (liftSub ty s)))) =-= SemSub s << pi1 << pi1. 
Proof.
intros.
rewrite LiftSubDef. rewrite tlConsMap. rewrite LiftSubDef. unfold shiftSub. rewrite shiftConsMap. rewrite tlConsMap.
rewrite SemShiftSub. by rewrite SemShiftSub.
Qed.

(*==========================================================================
  Semantic function commutes with substitution
  ==========================================================================*)

(*=SemCommutesWithSub *)
Lemma SemCommutesWithSub E:
   (forall t (v:Value E t) E' (s:Sub E E'), SemVal v << SemSub s =-= SemVal (subVal s v))
/\ (forall t (e:Exp   E t) E' (s:Sub E E'), SemExp e << SemSub s =-= SemExp (subExp s e)).
(*=End *)
Proof.
apply ExpVal_ind.

(* TINT *)
intros. simpl. rewrite <- const_com; trivial.

(* TBOOL *)
intros. simpl. rewrite <- const_com; trivial.

(* TVAR *)
intros E ty var E' s.
simpl.
unfold subVal. simpl travVal.
induction var. simpl.   rewrite prod_fun_snd.
destruct (consMapInv s) as [s' [v eq]]. subst.
simpl. rewrite hdConsMap. trivial.
destruct (consMapInv s) as [s' [v eq]]. subst.
simpl. 
specialize (IHvar s').
rewrite <- IHvar. rewrite <- comp_assoc.
rewrite tlConsMap. by rewrite prod_fun_fst.

(* TFIX *)
intros E t t1 body IH E' s. rewrite substTFIX. simpl. 
rewrite <- comp_assoc.
rewrite exp_comp. rewrite exp_comp. rewrite <- IH.
clear IH. simpl. do 2 rewrite comp_idL.
rewrite SemLift2Sub. rewrite <- comp_assoc. rewrite prod_fun_compl. by rewrite <- comp_assoc.

(* TPAIR *)
intros E t1 t2 v1 IH1 v2 IH2 E' s. rewrite substTPAIR. simpl. 
rewrite <- IH1. rewrite <- IH2. by rewrite prod_fun_compl.

(* TFST *)
intros E t1 t2 v IH E' s. rewrite substTFST. simpl. 
rewrite <- IH. by repeat (rewrite <- comp_assoc).

(* TSND *)
intros E t1 t2 v IH E' s. rewrite substTSND. simpl.
rewrite <- IH. by repeat (rewrite <- comp_assoc).

(* TOP *)
intros E n v1 IH1 v2 IH2 E' s. rewrite substTOP. simpl. 
repeat (rewrite <- comp_assoc). rewrite <- IH1. rewrite <- IH2.
by rewrite prod_fun_compl.

(* TGT *)
intros E v1 IH1 v2 IH2 E' s. rewrite substTGT. simpl. 
repeat (rewrite <- comp_assoc). rewrite <- IH1. rewrite <- IH2.
by rewrite prod_fun_compl.

(* TVAL *)
intros E t v IH E' s. rewrite substTVAL. simpl. 
rewrite <- IH. by rewrite <- comp_assoc.

(* TLET *)
intros E t1 t2 e2 IH2 e1 IH1 E' s. rewrite substTLET. simpl. 
rewrite <- comp_assoc.
specialize (IH2 _ s).
specialize (IH1 _ (liftSub _ s)).
rewrite prod_fun_compl.
rewrite KLEISLIR_comp.
rewrite <- IH2. clear IH2. rewrite <- IH1. clear IH1. simpl.
do 2 rewrite comp_idL. by rewrite SemLiftSub.

(* TAPP *)
intros E t1 t2 v1 IH1 v2 IH2 E' s. rewrite substTAPP. simpl. 
rewrite <- comp_assoc. rewrite <- IH1. rewrite <- IH2.
by rewrite prod_fun_compl.

(* TIF *)
intros E t ec IHc te1 IH1 te2 IH2 E' s. rewrite substTIF. simpl. 
rewrite choose_comp. rewrite <- IH1. rewrite <- IH2. by rewrite <- IHc.
Qed.