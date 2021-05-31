
(*begin hide*)
Add LoadPath "../domain-theory".
Require Import Utils.

(* new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(* endof new in 8.4 *)

From mathcomp Require Export ssreflect ssrnat ssrbool eqtype seq fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

Require Import Program.

(** *)
(*** Chapter 4: Extended Language Definition ***)
(** *)

Inductive OrdOp := EqOP | LeOP.

Inductive BoolOp := AndOP | OrOP.

Inductive NatOp := PlusOP | MinusOP.

Definition SemOrdOp (op : OrdOp) : nat -> nat -> bool :=
  match op with
  | EqOP => Coq.Init.Nat.eqb
  | LeOP => Coq.Init.Nat.leb
  end
.

Definition SemBoolOp (op : BoolOp) : bool -> bool -> bool :=
  match op with
  | AndOP => andb
  | OrOP => orb
  end
.

Definition SemNatOp (op : NatOp) : nat -> nat -> nat :=
  match op with
  | PlusOP  => Peano.plus
  | MinusOP => Peano.minus
  end
.

(** *Language Syntax *)
Definition Env := nat.

Inductive Var : Env -> Type :=
| ZVAR : forall E, Var (S E)
| SVAR : forall E, Var E -> Var (S E)
.

(** *Definition 36: Syntax *)
Inductive V E :=
| VAR   : Var E     -> V E
| BOOL  : bool        -> V E
| NAT   : nat        -> V E
| FUN   : Expr E.+2 -> V E
| VPAIR : V E       -> V E -> V E
with Expr E :=
| VAL  : V E    -> Expr E
| APP  : V E    -> V E       -> Expr E
| OOp  : OrdOp  -> Expr E    -> Expr E -> Expr E
| BOp  : BoolOp -> Expr E    -> Expr E -> Expr E
| NOp  : NatOp  -> Expr E    -> Expr E -> Expr E
| LET  : Expr E -> Expr E.+1 -> Expr E
| IFB  : Expr E -> Expr E    -> Expr E -> Expr E
| EFST  : V E   -> Expr E
| ESND  : V E   -> Expr E
.
Arguments BOOL [E] _.
Arguments NAT [E] _.

Scheme V_induction   := Induction for V Sort Prop
  with E_induction   := Induction for Expr Sort Prop.
Combined Scheme mutual_VE_induction from V_induction, E_induction.

(** *Definition 37: Frame Stack *)
Inductive FS :=
| Empty    : FS
| PUSHLet  : FS -> Expr 1 -> FS
| PUSHLOOp : OrdOp -> FS -> Expr 0 -> FS
| PUSHROOp : OrdOp -> FS -> Expr 0 -> FS
| PUSHLBOp : BoolOp -> FS -> Expr 0 -> FS
| PUSHRBOp : BoolOp -> FS -> Expr 0 -> FS
| PUSHLNOp : NatOp -> FS -> Expr 0 -> FS
| PUSHRNOp : NatOp -> FS -> Expr 0 -> FS
| PUSHCond : FS -> Expr 0 -> Expr 0 -> FS
.


(** *Notation *)
Notation "⎣ b ⎦" := (VAL (BOOL b)) (at level 1, no associativity).
Notation "⌊ n ⌋" := (VAL (NAT n)) (at level 1, no associativity).
Notation "'v⎨' v ⎬" := (VAR v) (at level 202, no associativity).
Notation "'e⎨' v ⎬" := (VAL (VAR v)) (at level 202, no associativity).
Notation "'λ' e" := (FUN e) (at level 1, no associativity).
Infix "@"        := APP (at level 201, left associativity).

Notation "∅" := Empty.
Infix "⊚" := PUSHLet (at level 1, left associativity).
Notation "fs ∘ ( e ⦓ op ⦔ ⊡ )" := (PUSHRNOp op fs e)
                                 (at level 1, left associativity).
Notation "fs ∘ ( ⊡ ⦓ op ⦔ e )" := (PUSHLNOp op fs e)
                                 (at level 1, left associativity).
Notation "fs ∘ ( e ⇆ e' )" := (PUSHCond fs e e')
                                 (at level 1, left associativity).

(*begin hide*)
(** *MAP Section *)
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
  
  Axiom MapExtensional : forall E E' (r1 r2 : Map E E'),
      (forall var, r1 var = r2 var) -> r1 = r2.
  
  Lemma hdConsMap : forall E E' (v : P E') (s : Map E E'), hdMap (consMap v s) = v. 
  Proof. by []. Qed.
  Lemma tlConsMap : forall E E' (v : P E') (s : Map E E'), tlMap (consMap v s) = s. 
  Proof. move => E E' v s. by apply MapExtensional. Qed.

  Import Program.
  Lemma consMapEta : forall E E' (m:Map (E.+1) E'), m = consMap (hdMap m) (tlMap m).
  Proof. move => E E' m. apply MapExtensional.
         intro. by dependent destruction var. 
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
      vl : forall E, P E -> V E;
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
  
  Definition shiftMap E E' (m : Map E E') : Map E (E'.+1) :=
    fun var => wk ops (m var).
  Definition idMap E : Map E E := fun (var : Var E) => vr ops var.
  
  Lemma shiftConsMap :
    forall E E' (m : Map E E') (x : P E'),
    shiftMap (consMap x m) = consMap (wk ops x) (shiftMap m). 
  Proof. intros E E' m x. apply MapExtensional. by dependent destruction var. Qed.
  
  Lemma LiftMapDef :
    forall E E' (m : Map E' E), lift m = consMap (vr ops (ZVAR _)) (shiftMap m).
  Proof. intros. apply MapExtensional. by dependent destruction var. Qed.
  
  Fixpoint travV {E E'} (v : V E) (m : Map E E') : V E' :=
    match v with
    | VAR v       => vl ops (m v)
    | BOOL b      => BOOL b
    | NAT i       => NAT i
    | FUN e       => FUN (travE e (lift (lift m)))
    | VPAIR v v'  => VPAIR (travV v m) (travV v' m)
    end
  with travE {E E'} (e : Expr E) : Map E E' -> Expr E' :=
    match e with
    | VAL v        => fun m => VAL    (travV v m)
    | APP v1 v2    => fun m => APP    (travV v1 m) (travV v2 m)
    | OOp op e1 e2 => fun m => OOp op (travE e1 m) (travE e2 m)
    | BOp op e1 e2 => fun m => BOp op (travE e1 m) (travE e2 m)
    | NOp op e1 e2 => fun m => NOp op (travE e1 m) (travE e2 m)
    | LET e1 e2    => fun m => LET    (travE e1 m) (travE e2 (lift m))
    | IFB e0 e1 e2 => fun m => IFB    (travE e0 m) (travE e1 m) (travE e2 m)
    | EFST v       => fun m => EFST   (travV v m)
    | ESND v       => fun m => ESND   (travV v m)
    end.
  
  Definition mapV E E' m v := @travV E E' v m.
  Definition mapE E E' m e := @travE E E' e m.
  
  Variable E E' : Env.
  Variable m : Map E E'.

  Lemma mapBOOL : forall (b : bool), mapV m (BOOL b) = BOOL b.
  Proof.
    intro. unfold mapV. unfold travV. destruct E. reflexivity. reflexivity.
  Qed.

  Lemma mapNAT : forall (n : nat), mapV m (NAT n) = NAT n.
  Proof.
    intro. unfold mapV. unfold travV. destruct E. reflexivity. reflexivity.
  Qed.
  
  Lemma mapVAR : forall (var : Var _),
      mapV m (VAR var) = vl ops (m var).
  Proof.
    intro. unfold mapV. by unfold travV.
  Qed.
  
  Lemma mapFUN : forall (e : Expr _),
      mapV m (FUN e) = FUN (mapE (lift (lift m)) e).
  Proof.
    intros e. unfold mapV. unfold mapE. by simpl.
  Qed.

  Lemma mapOOp : forall op e1 e2,
      mapE m (OOp op e1 e2) = OOp op (mapE m e1) (mapE m e2).
  Proof.
    intros. unfold mapV. unfold travV. destruct E. reflexivity. reflexivity.
  Qed.
  
  Lemma mapBOp : forall op e1 e2,
      mapE m (BOp op e1 e2) = BOp op (mapE m e1) (mapE m e2).
  Proof.
    intros. unfold mapV. unfold travV. destruct E. reflexivity. reflexivity.
  Qed.

  Lemma mapNOp : forall op e1 e2,
      mapE m (NOp op e1 e2) = NOp op (mapE m e1) (mapE m e2).
  Proof.
    intros. unfold mapV. unfold travV. destruct E. reflexivity. reflexivity.
  Qed.
  
  Lemma mapVAL : forall (v : V _), mapE m (VAL v) = VAL (mapV m v).
  Proof.
    intro. unfold mapV. unfold travV. destruct E. reflexivity. reflexivity.
  Qed.
  
  Lemma mapAPP : forall (v v': V _), mapE m (APP v v') = APP (mapV m v) (mapV m v').
  Proof.
    intros v v'. unfold mapV. unfold mapE. unfold travE. destruct E.
    reflexivity. reflexivity.
  Qed.
  
  Lemma mapLET : forall (e1 : Expr _) (e2 : Expr _),
      mapE m (LET e1 e2) = LET (mapE m e1) (mapE (lift m) e2).
  Proof.
    intro. unfold mapV. unfold travV. destruct E. reflexivity. reflexivity.
  Qed.

  Lemma mapIFB : forall (e0 e1 e2 : Expr _),
      mapE m (IFB e0 e1 e2) = IFB (mapE m e0) (mapE m e1) (mapE m e2).
  Proof.
    auto.
  Qed.

  Lemma mapPAIR : forall (v v' : V _),
      mapV m (VPAIR v v') = VPAIR (mapV m v) (mapV m v').
  Proof.
    auto.
  Qed.

  Lemma mapFST : forall (v : V _),
      mapE m (EFST v) = EFST (mapV m v).
  Proof.
    auto.
  Qed.

  Lemma mapSND : forall (v : V _),
      mapE m (ESND v) = ESND (mapV m v).
  Proof.
    auto.
  Qed.
  
  Lemma liftIdMap : lift (@idMap E) = @idMap (E.+1).
  Proof.
    apply MapExtensional. dependent destruction var; [by [] | by apply wkvr].  
  Qed.
  
  Lemma idMapDef :
    @idMap (E.+1) = consMap (vr ops (ZVAR _)) (shiftMap (@idMap E)).
  Proof.
    apply MapExtensional. dependent destruction var; first by [].
    unfold idMap, shiftMap. simpl. by rewrite wkvr.
  Qed.

End MAP.
  
Hint Rewrite mapVAR mapNAT mapFUN mapNOp mapVAL mapAPP mapLET mapIFB : mapHints.

Arguments idMap [P] _ _ _.

Lemma applyIdMap P (ops:MapOps P) E : 
  (forall (v : V E), mapV ops (idMap ops E) v = v)
  /\
  (forall (e : Expr E), mapE ops (idMap ops E) e = e).
Proof.
  intros P ops.
  apply mutual_VE_induction.
  - Case "V".
    + SCase "v = VAR ...".
      intros E v.
      rewrite -> mapVAR.
      apply vlvr.
    + SCase "v = BOOL ...".
      intros E b.
        by rewrite -> mapBOOL.
    + SCase "v = NAT ...".
      intros E n.
        by rewrite -> mapNAT.
    + SCase "v = FUN ...".
      intros E e H.
      rewrite -> mapFUN.
      repeat (rewrite -> liftIdMap).
        by rewrite -> H.
    + SCase "v = PAIR ...".
      intros E v H v' H'.
      rewrite -> mapPAIR.
        by rewrite -> H, H'.
  - Case "Expr".
    + SCase "e = VAL v".
      intros E v H.
      rewrite -> mapVAL.
        by rewrite -> H.
    + SCase "e = APP v1 v2".
      intros E v1 H v2 H0.
      rewrite -> mapAPP.
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = OOp op e1 e2".
      intros E op e1 H e2 H0.
      rewrite -> mapOOp.
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = BOp op e1 e2".
      intros E op e1 H e2 H0.
      rewrite -> mapBOp.
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = NOp op e1 e2".
      intros E op e1 H e2 H0.
      rewrite -> mapNOp.
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = LET e1 e2".
      intros E e1 H e2 H0.
      rewrite -> mapLET.
      rewrite -> H.
      rewrite -> liftIdMap.
        by rewrite -> H0.
    + SCase "e = IFB e0 e1 e2".
      intros E e0 H0 e1 H1 e2 H2.
      rewrite -> mapIFB.
        by rewrite -> H0, -> H1, -> H2.
    + SCase "e = FST v".
      intros E v H.
      rewrite -> mapFST.
        by rewrite -> H.
    + SCase "e = SND v".
      intros E v H.
      rewrite -> mapSND.
        by rewrite -> H.
Qed.

(** *RENAMING Section *)
Definition Ren := Map Var.

(** update for 8.4 *)
Definition RenMapOps := (@Build_MapOps _ (fun _ v => v)
                                      VAR SVAR
                                      (fun _ _ => Logic.eq_refl)
                                      (fun _ _ => Logic.eq_refl)
                       ).

Definition renV := mapV RenMapOps.
Definition renE := mapE RenMapOps.
Definition liftRen := lift RenMapOps.
Definition shiftRen := shiftMap RenMapOps.
Definition idRen := idMap RenMapOps.
Arguments idRen : clear implicits.

(*==========================================================================
  Composition of renaming
  ==========================================================================*)

Definition composeRen P E E' E''
           (m : Map P E' E'') (r : Ren E E') : Map P E E''
  := fun var => m (r var). 

Lemma liftComposeRen : forall P ops E E' E''
                         (m:Map P E' E'') (r:Ren E E'),
    lift ops (composeRen m r) = composeRen (lift ops m) (liftRen r).
Proof. intros. apply MapExtensional. by dependent destruction var. Qed.

Lemma applyComposeRen E : 
  (forall (v : V E) P ops E' E'' (m:Map P E' E'') (s : Ren E E'),
      mapV ops (composeRen m s) v = mapV ops m (renV s v))
  /\ (forall (e : Expr E) P ops E' E'' (m:Map P E' E'') (s : Ren E E'),
        mapE ops (composeRen m s) e = mapE ops m (renE s e)).
Proof.
  apply mutual_VE_induction.
  - Case "V".
    + SCase "v = VAR".
      intros E v P ops E' E'' m s.
      rewrite -> mapVAR.
      unfold renV. repeat (rewrite -> mapVAR).
        by unfold composeRen.
    + SCase "v = BOOL".
      intros E n P ops E' E'' m s.
      unfold renV.
        by repeat (rewrite -> mapBOOl).
    + SCase "v = NAT".      
      intros E n P ops E' E'' m s.
      unfold renV.
        by repeat (rewrite -> mapNAT).
    + SCase "v = FUN".
      intros E e H P ops E' E'' m s.
      unfold renV.
      repeat (rewrite -> mapFUN).
      repeat (rewrite -> liftComposeRen).
        by rewrite -> H.
    + SCase "v = PAIR ...".
      intros E v H v' H' P ops E' E'' m s.
      rewrite -> mapPAIR.
        by rewrite -> H, H'.
  - Case "Expr".
    + SCase "e = VAL v".
      intros E v H P ops E' E'' m s.
      rewrite -> mapVAL.
        by rewrite -> H.
    + SCase "e = APP v1 v2".
      intros E v1 H v2 H0 P ops E' E'' m s.
      unfold renE.
      repeat (rewrite -> mapAPP).
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = OOp op e1 e2".
      intros E op e1 H e2 H0 P ops E' E'' m s.
      unfold renE.
      repeat (rewrite -> mapOOp).
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = BOp op e1 e2".
      intros E op e1 H e2 H0 P ops E' E'' m s.
      unfold renE.
      repeat (rewrite -> mapBOp).
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = NOp op e1 e2".
      intros E op e1 H e2 H0 P ops E' E'' m s.
      unfold renE.
      repeat (rewrite -> mapNOp).
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = LET e1 e2".
      intros E e1 H e2 H0 P ops E' E'' m s.
      unfold renE.
      repeat (rewrite -> mapLET).
      rewrite -> H.
      rewrite -> liftComposeRen.
        by rewrite -> H0.
    + SCase "e = IFB e0 e1 e2".
      intros E e0 H0 e1 H1 e2 H2 P ops E' E'' m s.
      unfold renE.
      do 2 rewrite -> mapIFB.
      rewrite -> H0, -> H1, -> H2. auto.
    + SCase "e = FST v".
      intros E v H P ops E' E'' m s.
      unfold renE.
      do 2 rewrite -> mapFST.
        by rewrite -> H.
    + SCase "e = SND v".
      intros E v H P ops E' E'' m s.
      unfold renE.
      do 2 rewrite -> mapSND.
        by rewrite -> H.
Qed.

(** *Substitution Section *)
Definition Sub := Map V.
(** update for 8.4 *)

Definition SubMapOps : MapOps V :=
  (@Build_MapOps _ VAR (fun _ v => v)
                 (fun E => renV (fun v => SVAR v))
                 (fun _ _ => Logic.eq_refl)
                 (fun _ _ => Logic.eq_refl)
  ).

Definition subV := mapV SubMapOps.
Definition subE := mapE SubMapOps.
Definition shiftSub := shiftMap SubMapOps.
Definition liftSub := lift SubMapOps.
Definition idSub := idMap SubMapOps.
Arguments idSub : clear implicits.

(** *Notation *)
Notation "[ x , .. , y ]" :=
  (consMap x .. (consMap y (idSub _)) ..) : Sub_scope.
Delimit Scope Sub_scope with subst.
Arguments subV _ _ _%Sub_scope _.
Arguments subE _ _ _%Sub_scope _.

Notation "v ⎧ δ ⎫" := (@subV _ _ δ v) (at level 1, no associativity).
Notation "e ⎩ δ ⎭" := (@subE _ _ δ e) (at level 1, no associativity).

Ltac UnfoldRenSub := (unfold subV; unfold subE; unfold renV;
                     unfold renE; unfold liftSub; unfold liftRen
                    ).
Ltac FoldRenSub := (fold subV; fold subE; fold renV; fold renE;
                   fold liftSub; fold liftRen
                  ).
Ltac SimplMap := (UnfoldRenSub; autorewrite with mapHints; FoldRenSub).

(*==========================================================================
  Composition of substitution followed by renaming
  ==========================================================================*)

Definition composeRenSub E E' E'' (r : Ren E' E'') (s : Sub E E') : Sub E E'' :=
  fun var => renV r (s var)
.

Lemma liftComposeRenSub : forall E E' E'' (r:Ren E' E'') (s:Sub E E'),
    liftSub (composeRenSub r s) = composeRenSub (liftRen r) (liftSub s).
Proof.
  intros. apply MapExtensional. dependent destruction var; first by [].
  simpl. unfold composeRenSub. unfold liftSub. unfold renV at 1.
  rewrite <- (proj1 (applyComposeRen _)). unfold lift. simpl wk. unfold renV.
  rewrite <- (proj1 (applyComposeRen _)). reflexivity.
Qed.

Lemma applyComposeRenSub E : 
  (forall (v : V E) E' E'' (r : Ren E' E'') (s : Sub E E'),
      subV (composeRenSub r s) v = renV r (subV s v))
  /\
  (forall (e : Expr E) E' E'' (r : Ren E' E'') (s : Sub E E'),
      subE (composeRenSub r s) e = renE r (subE s e)).
Proof.
  apply mutual_VE_induction.
  - Case "V".
    + SCase "v = VAR".
      intros E v E' E'' r s.
        by SimplMap.
    + SCase "v = BOOL".      
      intros E n E' E'' r s.
        by SimplMap.
    + SCase "v = NAT".      
      intros E n E' E'' r s.
        by SimplMap.
    + SCase "v = FUN".
      intros E e H E' E'' r s.
      unfold "_ ⎧ _ ⎫".
      rewrite -> mapFUN.
      repeat (rewrite -> liftComposeRenSub).
        by rewrite -> H.
    + SCase "v = PAIR ...".
      intros E v H v' H' E' E'' r s.
      unfold "_ ⎧ _ ⎫".
      rewrite -> mapPAIR.
        by rewrite -> H, H'.
  - Case "Expr".
    + SCase "e = VAL v".
      intros E v H E' E'' r s.
      unfold "_ ⎩ _ ⎭".
      rewrite -> mapVAL.
        by rewrite -> H.
    + SCase "e = APP v1 v2".
      intros E v1 H v2 H0 E' E'' r s.
      unfold "_ ⎩ _ ⎭".
      repeat (rewrite -> mapAPP).
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = OOp e1 e2".
      intros E op e1 H e2 H0 E' E'' r s.
      unfold "_ ⎩ _ ⎭".
      repeat (rewrite -> mapOOp).
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = BOp e1 e2".
      intros E op e1 H e2 H0 E' E'' r s.
      unfold "_ ⎩ _ ⎭".
      repeat (rewrite -> mapBOp).
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = NOp e1 e2".
      intros E op e1 H e2 H0 E' E'' r s.
      unfold "_ ⎩ _ ⎭".
      repeat (rewrite -> mapNOp).
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = LET e1 e2".
      intros E e1 H e2 H0 E' E'' r s.
      unfold "_ ⎩ _ ⎭".
      repeat (rewrite -> mapLET).
      rewrite -> H.
      rewrite -> liftComposeRenSub.
        by rewrite -> H0.
    + SCase "e = IFB e0 e1 e2".
      intros E e0 H0 e1 H1 e2 H2 E' E'' r s.
      unfold "_ ⎩ _ ⎭", renE.
      do 2 rewrite -> mapIFB.
      rewrite -> H0, -> H1, -> H2. auto.
    + SCase "e = FST v".
      intros E v H E' E'' r s.
      unfold "_ ⎩ _ ⎭", renE.
      do 2 rewrite -> mapFST.
        by rewrite -> H.
    + SCase "e = SND v".
      intros E v H E' E'' r s.
      unfold "_ ⎩ _ ⎭", renE.
      do 2 rewrite -> mapSND.
        by rewrite -> H.
Qed.

(*==========================================================================
  Composition of substitutions
  ==========================================================================*)

Definition composeSub E E' E'' (s' : Sub E' E'') (s : Sub E E') : Sub E E''
  := fun var => subV s' (s var).
Arguments composeSub _ _ _ _%Sub_scope _%Sub_scope _.

Lemma liftComposeSub : forall E E' E'' (s' : Sub E' E'') (s : Sub E E'),
    liftSub (composeSub s' s) = composeSub (liftSub s') (liftSub s).
  intros. apply MapExtensional. dependent destruction var; first by []. 
  unfold composeSub. simpl liftSub.
  rewrite <- (fst (applyComposeRenSub _)). unfold composeRenSub. unfold subV.
    by rewrite <- (fst (applyComposeRen _)).
Qed.

Lemma substComposeSub E :
  (forall (v : V E) E' E'' (s' : Sub E' E'') (s : Sub E E'),
      subV (composeSub s' s) v = subV s' (subV s v))
  /\
  (forall (e : Expr E) E' E'' (s' : Sub E' E'') (s : Sub E E'),
      subE (composeSub s' s) e = subE s' (subE s e)).
Proof.  
  apply mutual_VE_induction.
  - Case "V".
    + SCase "v = VAR".
      intros E v E' E'' s' s.
      unfold "_ ⎧ _ ⎫".
        by repeat (rewrite -> mapVAR).
    + SCase "v = BOOL".
      intros E n E' E'' s' s.
      unfold "_ ⎧ _ ⎫".
        by repeat (rewrite -> mapBOOl).
    + SCase "v = NAT".
      intros E n E' E'' s' s.
      unfold "_ ⎧ _ ⎫".
        by repeat (rewrite -> mapNAT).
    + SCase "v = FUN".
      intros E e H E' E'' s' s.
      unfold "_ ⎧ _ ⎫".
      repeat (rewrite -> mapFUN).
      repeat (rewrite -> liftComposeSub).
        by rewrite -> H.
    + SCase "v = PAIR ...".
      intros E v H v' H' E' E'' s' s.
      unfold "_ ⎧ _ ⎫".
      rewrite -> mapPAIR.
        by rewrite -> H, H'.
  - Case "Expr".
    + SCase "e = VAL v".
      intros E v H E' E'' s' s.
      unfold "_ ⎩ _ ⎭".
      repeat (rewrite -> mapVAL).
        by rewrite -> H.
    + SCase "e = APP v1 v2".
      intros E v1 H v2 H0 E' E'' s' s.
      unfold "_ ⎩ _ ⎭".
      repeat (rewrite -> mapAPP).
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = OOp e1 e2".
      intros E op e1 H e2 H0 E' E'' s' s.
      unfold "_ ⎩ _ ⎭".
      repeat (rewrite -> mapOOp).
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = BOp e1 e2".
      intros E op e1 H e2 H0 E' E'' s' s.
      unfold "_ ⎩ _ ⎭".
      repeat (rewrite -> mapBOp).
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = NOp e1 e2".
      intros E op e1 H e2 H0 E' E'' s' s.
      unfold "_ ⎩ _ ⎭".
      repeat (rewrite -> mapNOp).
      rewrite -> H.
        by rewrite -> H0.
    + SCase "e = LET e1 e2".
      intros E e1 H e2 H0 E' E'' s' s.
      unfold "_ ⎩ _ ⎭".
      repeat (rewrite -> mapLET).
      rewrite -> H.
      rewrite -> liftComposeSub.
        by rewrite -> H0.
    + SCase "e = IFB e0 e1 e2".
      intros E e0 H0 e1 H1 e2 H2 E' E'' r s.
      unfold "_ ⎩ _ ⎭", renE.
      do 2 rewrite -> mapIFB.
      rewrite -> H0, -> H1, -> H2. auto.
    + SCase "e = FST v".
      intros E v H E' E'' s' s.
      unfold "_ ⎩ _ ⎭", renE.
      do 2 rewrite -> mapFST.
        by rewrite -> H.
    + SCase "e = SND v".
      intros E v H E' E'' s' s.
      unfold "_ ⎩ _ ⎭", renE.
      do 2 rewrite -> mapSND.
        by rewrite -> H.        
Qed.

(** updated for 8.4 *)
Lemma composeCons : forall E E' E'' (s':Sub E' E'') (s:Sub E E') (v:V _), 
    composeSub (consMap v s') (liftSub s) = consMap v (composeSub s' s).
  intros. apply MapExtensional. dependent destruction var; first by [].
  unfold composeSub. simpl consMap. unfold subV. unfold liftSub.
  unfold lift. simpl wk. rewrite <- (fst (applyComposeRen _)). 
  unfold composeRen. auto.
Qed.

Lemma composeSubIdLeft : forall E E' (s : Sub E E'), composeSub (idSub _) s = s.
Proof. intros. apply MapExtensional.  intros var.
       apply (proj1 (applyIdMap _ _)).
Qed.

Lemma composeSubIdRight : forall E E' (s:Sub E E'), composeSub s (idSub _) = s.
Proof.
  destruct E. by []. by [].
Qed.

(*end hide*)
