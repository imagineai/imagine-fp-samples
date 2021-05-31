(**********************************************************************************
 * unii.v                                                                   *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * July 2010                                                                      *
 * Build with Coq 8.2pl1 plus SSREFLECT                                           *
 **********************************************************************************)

(* Unityped lambda calculus, well-scoped by construction *)

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

From mathcomp Require Export ssreflect ssrnat ssrbool eqtype seq fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition Env := nat.

Inductive Var : Env -> Type :=
| ZVAR : forall E, Var (S E)
| SVAR : forall E, Var E -> Var (S E).

Inductive Value E :=
| VAR: Var E -> Value E
| INT: nat -> Value E
| LAMBDA: Exp (S E) -> Value E
with Exp E :=
| VAL: Value E -> Exp E
| APP: Value E -> Value E -> Exp E
| LET: Exp E -> Exp (S E) -> Exp E
| IFZ: Value E -> Exp E -> Exp E -> Exp E
| OP: (nat -> nat -> nat) -> Value E -> Value E -> Exp E.
Implicit Arguments INT [E].

Scheme Value_ind2 := Induction for Value Sort Prop
  with Exp_ind2   := Induction for Exp Sort Prop.
Combined Scheme ExpValue_ind from Value_ind2, Exp_ind2.

(*==========================================================================
  Variable-domain maps. 
  By instantiating P with Var we get renamings.
  By instantiating P with Value we get substitutions.
  ==========================================================================*)
Section MAP.

  Variable P : Env -> Type.
  Definition Map E E' := Var E -> P E'.

  (* Head, tail and cons *)
  Definition tlMap E E' (m:Map (E.+1) E') : Map E E' := fun v => m (SVAR v).
  Definition hdMap E E' (m:Map (E.+1) E') : P E' := m (ZVAR _).

  Definition consMap E E' (hd: P E') (tl : Map E E') : Map (E.+1) E' :=
  (fun var =>
    match var in Var p return (Map (p.-1) E') -> P E' with 
      | ZVAR _ => fun _ => hd
      | SVAR _ var' => fun tl' => tl' var'
    end tl). 

  Axiom MapExtensional : forall E E' (r1 r2 : Map E E'), (forall var, r1 var = r2 var) -> r1 = r2.

  Lemma hdConsMap : forall E E' (v : P E') (s : Map E E'), hdMap (consMap v s) = v. 
  Proof. by []. Qed.
  Lemma tlConsMap : forall E E' (v : P E') (s : Map E E'), tlMap (consMap v s) = s. 
  Proof. move => E E' v s. by apply MapExtensional. Qed.

  Require Import Program.
  Lemma consMapEta : forall E E' (m:Map (E.+1) E'), m = consMap (hdMap m) (tlMap m).
  Proof. move => E E' m. apply MapExtensional. by dependent destruction var. 
  Qed.

  (*==========================================================================
    Package of operations used with a Map
      vr maps a Var into Var or Value (so is either the identity or TVAR)
      vl maps a Var or Value to a Value (so is either TVAR or the identity)
      wk weakens a Var or Value (so is either SVAR or renaming through SVAR on a value)
    ==========================================================================*)
  Record MapOps :=
  {
    vr : forall E, Var E -> P E;   
    vl : forall E, P E -> Value E;
    wk : forall E, P E -> P (E.+1);
    wkvr : forall E (var : Var E), wk (vr var) = vr (SVAR var);
    vlvr : forall E (var : Var E), vl (vr var) = VAR var
  }.
  Variable ops : MapOps.

  Definition lift E E' (m : Map E E') : Map (E.+1) (E'.+1) :=
  (fun var => match var in Var p return Map (p.-1) E' -> P (E'.+1) with
  | ZVAR _ => fun _ => vr ops (ZVAR _)
  | SVAR _ x => fun m => wk ops (m x)
  end m).

  Definition shiftMap E E' (m : Map E E') : Map E (E'.+1) := fun var => wk ops (m var).
  Definition idMap E : Map E E := fun (var : Var E) => vr ops var.

  Lemma shiftConsMap : forall E E' (m : Map E E') (x : P E'), shiftMap (consMap x m) = consMap (wk ops x) (shiftMap m). 
  Proof. intros E E' m x. apply MapExtensional. by dependent destruction var. Qed.

  Lemma LiftMapDef : forall E E' (m : Map E' E), lift m = consMap (vr ops (ZVAR _)) (shiftMap m).
  Proof. intros. apply MapExtensional. by dependent destruction var. Qed.

  Fixpoint travVal E E' (v : Value E) : Map E E' -> Value E' :=
  match v with
    | VAR v => fun m => vl ops (m v)
    | INT i => fun m => INT i
    | LAMBDA e => fun m => LAMBDA (travExp e (lift m))
  end
  with travExp E E' (e : Exp E) : Map E E' -> Exp E' :=
  match e with
    | VAL v => fun m => VAL (travVal v m)
    | APP v0 v1 => fun m => APP (travVal v0 m) (travVal v1 m)
    | LET e0 e1 => fun m => LET (travExp e0 m) (travExp e1 (lift m))
    | OP op v0 v1 => fun m => OP op (travVal v0 m) (travVal v1 m)
    | IFZ v e0 e1 => fun m => IFZ (travVal v m) (travExp e0 m) (travExp e1 m)
  end.

  Definition mapVal E E' m v := @travVal E E' v m.
  Definition mapExp E E' m e := @travExp E E' e m.

  Variable E E' : Env.
  Variable m : Map E E'.
  Lemma mapVAR : forall (var : Var _), mapVal m (VAR var) = vl ops (m var). by []. Qed. 
  Lemma mapINT : forall n, mapVal m (INT n) = INT n. by []. Qed.
  Lemma mapLAMBDA : forall (e : Exp _), mapVal m (LAMBDA e) = LAMBDA (mapExp (lift m) e). by []. Qed.
  Lemma mapOP : forall op v1 v2, mapExp m (OP op v1 v2) = OP op (mapVal m v1) (mapVal m v2). by []. Qed.
  Lemma mapVAL : forall (v : Value _), mapExp m (VAL v) = VAL (mapVal m v). by []. Qed.
  Lemma mapLET : forall (e1 : Exp _) (e2 : Exp _), mapExp m (LET e1 e2) = LET (mapExp m e1) (mapExp (lift m) e2). by []. Qed.
  Lemma mapIFZ : forall v (e1 e2 : Exp _), mapExp m (IFZ v e1 e2) = IFZ (mapVal m v) (mapExp m e1) (mapExp m e2). by []. Qed.
  Lemma mapAPP : forall (v1 : Value _) v2, mapExp m (APP v1 v2) = APP (mapVal m v1) (mapVal m v2). by []. Qed.

  Lemma liftIdMap : lift (@idMap E) = @idMap (E.+1).
  Proof. apply MapExtensional. dependent destruction var; [by [] | by apply wkvr].  
  Qed.

  Lemma idMapDef : @idMap (E.+1) = consMap (vr ops (ZVAR _)) (shiftMap (@idMap E)).
  Proof. apply MapExtensional. dependent destruction var; first by []. unfold idMap, shiftMap. simpl. by rewrite wkvr. Qed.

End MAP.

Hint Rewrite mapVAR mapINT mapLAMBDA mapOP mapVAL mapLET mapIFZ mapAPP : mapHints.

Implicit Arguments idMap [P]. 

Lemma applyIdMap P (ops:MapOps P) E : 
     (forall (v : Value E), mapVal ops (idMap ops E) v = v)
  /\ (forall (e : Exp E), mapExp ops (idMap ops E) e = e).
Proof.
  move => P ops.
  apply ExpValue_ind; intros; autorewrite with mapHints; try rewrite liftIdMap; try rewrite liftIdMap; try rewrite H; try rewrite H0; try rewrite H1; auto. by apply vlvr. 
Qed.

(*==========================================================================
  Variable renamings: Map Var
  ==========================================================================*)

Definition Ren := Map Var. 

(** update for 8.4 *)
Definition RenMapOps := (@Build_MapOps _ (fun _ v => v) VAR SVAR (fun _ _ => Logic.eq_refl) (fun _ _ => Logic.eq_refl)).

Definition renVal := mapVal RenMapOps.
Definition renExp := mapExp RenMapOps.
Definition liftRen := lift RenMapOps.
Definition shiftRen := shiftMap RenMapOps.
Definition idRen := idMap RenMapOps.
Implicit Arguments idRen []. 

(*==========================================================================
  Composition of renaming
  ==========================================================================*)

Definition composeRen P E E' E'' (m : Map P E' E'') (r : Ren E E') : Map P E E'' := fun var => m (r var). 

Lemma liftComposeRen : forall P ops E E' E'' (m:Map P E' E'') (r:Ren E E'), lift ops (composeRen m r) = composeRen (lift ops m) (liftRen r).
Proof. intros. apply MapExtensional. by dependent destruction var. Qed.

Lemma applyComposeRen E : 
   (forall (v : Value E) P ops E' E'' (m:Map P E' E'') (s : Ren E E'),
    mapVal ops (composeRen m s) v = mapVal ops m (renVal s v))
/\ (forall (e : Exp   E) P ops E' E'' (m:Map P E' E'') (s : Ren E E'),
    mapExp ops (composeRen m s) e = mapExp ops m (renExp s e)).
Proof.
apply ExpValue_ind; intros; autorewrite with mapHints; try rewrite liftComposeRen; try rewrite H;
try rewrite H0; try rewrite H1; auto.  
Qed.

(*==========================================================================
  Substitution
  ==========================================================================*)

Definition Sub := Map Value.
(** update for 8.4 *)
Definition SubMapOps : MapOps Value := (@Build_MapOps _ VAR (fun _ v => v) (fun E => renVal (fun v => SVAR v)) (fun _ _ => Logic.eq_refl) (fun _ _ => Logic.eq_refl)). 

Definition subVal := mapVal SubMapOps.
Definition subExp := mapExp SubMapOps.
Definition shiftSub := shiftMap SubMapOps.
Definition liftSub := lift SubMapOps.
Definition idSub := idMap SubMapOps.
Implicit Arguments idSub [].

Notation "[ x , .. , y ]" := (consMap x .. (consMap y (idSub _)) ..) : Sub_scope. 
Delimit Scope Sub_scope with subst.
Arguments Scope subExp [_ _ Sub_scope]. 
Arguments Scope subVal [_ _ Sub_scope]. 

Ltac UnfoldRenSub := (unfold subVal; unfold subExp; unfold renVal; unfold renExp; unfold liftSub; unfold liftRen).
Ltac FoldRenSub := (fold subVal; fold subExp; fold renVal; fold renExp; fold liftSub; fold liftRen).
Ltac SimplMap := (UnfoldRenSub; autorewrite with mapHints; FoldRenSub).

(*==========================================================================
  Composition of substitution followed by renaming
  ==========================================================================*)

Definition composeRenSub E E' E'' (r : Ren E' E'') (s : Sub E E') : Sub E E'' := fun var => renVal r (s var). 

Lemma liftComposeRenSub : forall E E' E'' (r:Ren E' E'') (s:Sub E E'), liftSub (composeRenSub r s) = composeRenSub (liftRen r) (liftSub s).
intros. apply MapExtensional. dependent destruction var; first by []. 
simpl. unfold composeRenSub. unfold liftSub. simpl. unfold renVal at 1.
rewrite <- (proj1 (applyComposeRen _)). unfold renVal. by rewrite <- (proj1 (applyComposeRen _)). 
Qed.

Lemma applyComposeRenSub E :
   (forall (v:Value E) E' E'' (r:Ren E' E'') (s : Sub E E'),
    subVal (composeRenSub r s) v = renVal r (subVal s v))
/\ (forall (e:Exp   E) E' E'' (r:Ren E' E'') (s : Sub E E'),
    subExp (composeRenSub r s) e = renExp r (subExp s e)).
Proof.
apply ExpValue_ind; (intros; SimplMap; try rewrite liftComposeRenSub; try rewrite H; try rewrite H0; try rewrite H1; auto). 
Qed.

(*==========================================================================
  Composition of substitutions
  ==========================================================================*)

Definition composeSub E E' E'' (s' : Sub E' E'') (s : Sub E E') : Sub E E'' := fun var => subVal s' (s var). 

Arguments Scope composeSub [_ _ _ Sub_scope Sub_scope]. 

Lemma liftComposeSub : forall E E' E'' (s' : Sub E' E'') (s : Sub E E'), liftSub (composeSub s' s) = composeSub (liftSub s') (liftSub s).
intros. apply MapExtensional. dependent destruction var; first by []. 
unfold composeSub. simpl.
rewrite <- (proj1 (applyComposeRenSub _)). unfold composeRenSub. unfold subVal. by rewrite <- (proj1 (applyComposeRen _)). 
Qed.

Lemma substComposeSub E : 
   (forall (v : Value E) E' E'' (s' : Sub E' E'') (s : Sub E E'),
    subVal (composeSub s' s) v = subVal s' (subVal s v))
/\ (forall (e : Exp   E) E' E'' (s' : Sub E' E'') (s : Sub E E'),
    subExp (composeSub s' s) e = subExp s' (subExp s e)).
Proof.
apply ExpValue_ind; (intros; SimplMap; try rewrite liftComposeSub; try rewrite H; try rewrite H0; try rewrite H1; auto). 
Qed.

(** updated for 8.4 *)
Lemma composeCons : forall E E' E'' (s':Sub E' E'') (s:Sub E E') (v:Value _), 
  composeSub (consMap v s') (liftSub s) = consMap v (composeSub s' s).
intros. apply MapExtensional. dependent destruction var; first by [].
unfold composeSub. simpl. unfold subVal. rewrite <- (proj1 (applyComposeRen _)). unfold composeRen. auto.
Qed.

Lemma composeSubIdLeft : forall E E' (s : Sub E E'), composeSub (idSub _) s = s.
Proof. intros. apply MapExtensional.  intros var. apply (proj1 (applyIdMap _ _)). Qed.

Lemma composeSubIdRight : forall E E' (s:Sub E E'), composeSub s (idSub _) = s.
Proof. intros. by apply MapExtensional. Qed.


