(**********************************************************************************
 * mpremet.v                                                                      *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * July 2010                                                                      *
 * Build with Coq 8.2pl1 plus SSREFLECT                                           *
 **********************************************************************************)

(* Preordered complete bounded ultrametric spaces *)

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

(** 8.5pl1 *)
Set Nonrecursive Elimination Schemes.
(** *)

From mathcomp Require Import ssreflect ssrbool eqtype.
Require Export PredomCore MetricCore Finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope C_scope.
Open Scope O_scope.
Open Scope M_scope.

(*=PreCBUmet *)
Module PreCBUmet.
  Definition respect (S:setoidType) (le:S -> S -> Prop) := 
    forall s s' t t':S, s =-= s' -> t =-= t' -> le s t -> le s' t'.
  Definition axiom (T:cmetricType) (le:T -> T -> Prop) :=
     respect le /\ forall c c' : cchain T, (forall i, le (c i) (c' i)) ->
                                   le (umet_complete c) (umet_complete c'). (*CLEAR*) 
  Record mixin_of (T:cmetricType) : Type := Mixin
  { pre :> PreOrd.mixin_of T; _ : @axiom T (@Ole (PreOrd.Pack pre T)); _ : T }.

  Record class_of (T:Type) := Class 
  { base :> CMetric.class_of T; mixin : mixin_of (CMetric.Pack base T) }.

  Coercion base2 T (c:class_of T) : PreOrd.class_of T := mixin c.

  Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
  Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
  Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
    let: Pack T c _ := cT return K _ (class cT) in k _ c.
  Definition repack (cT:type) : _ -> Type -> type := let k T c p := p c in unpack k cT.

  Definition pack := let k T c m := Pack (@Class T c m) T in CMetric.unpack k.

  Definition ordType (cT:type) := PreOrd.Pack (class cT) cT.
  Coercion cmetricType (cT:type) := CMetric.Pack (class cT) cT.
  Definition metricType (cT:type) := Metric.Pack (class cT) cT.
  Definition setoidType (cT:type) := Setoid.Pack (class cT) cT.

  Definition getelem (cT:type) : cT := let: Mixin _ _ e := mixin (class cT) in e.
(*CLEARED*) 
End PreCBUmet.
(*=End *)

Notation PCMMixin := PreCBUmet.Mixin.
Notation pcmType := PreCBUmet.type.
Notation PCMType := PreCBUmet.pack.

Canonical Structure PreCBUmet.ordType.
Canonical Structure PreCBUmet.cmetricType.
Canonical Structure PreCBUmet.metricType.
Canonical Structure PreCBUmet.setoidType.

Lemma pcm_chain_mono (T:pcmType) (c c':cchain T) : (forall i, c i <= c' i) -> umet_complete c <= umet_complete c'.
case => T. case. move => b. case. move => p A e. move => T' c c' C. apply A. by apply C.
Qed.

Lemma pcm_respect (T:pcmType) (x x' y y':T) : x =-= x' -> y =-= y' -> x <= y -> x' <= y'.
case => T. case. move => b. case. simpl. move => p A T' x x' y y' e e'. by apply (proj1 A).
Qed.

Definition pcm_getElem (T:pcmType) : T := PreCBUmet.getelem T.

(*=pcm_morphisms *)
Module FPCM. Section fpcm.
  Variable O1 O2 : pcmType.
  Record class_of (f:O1 -> O2) :=
    Class { base :> FMet.mixin_of f; ext :> FMon.mixin_of f }.
  Coercion base2 f (c:class_of f) : FMon.mixin_of f := fmonoMixin c. (*CLEAR*) 

  Structure type : Type := Pack {sort :> O1 -> O2; _ : class_of sort; _ : O1 -> O2}.
  Definition class (cT:type) := let: Pack _ c _ := cT return class_of cT in c.
  Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
    let: Pack T c _ := cT return K _ (class cT) in k _ c.
  Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.
  Definition pack := let k T c m := Pack (@Class T c m) T in FMet.unpack k.

  Coercion fmet f : fmet O1 O2 := FMet.Pack (class f) f.
  Definition fset f : fset O1 O2 := FSet.Pack (class f) f.
  Coercion fmono f : fmono _ _ := FMon.Pack (class f) f.

(*CLEARED*) 
End fpcm. End FPCM.
Notation fpcm := FPCM.type.
(*=End *)
Notation fpcmType := FPCM.pack.

Canonical Structure FPCM.fset.
Canonical Structure FPCM.fmono.
Canonical Structure FPCM.fmet.

Definition mk_fpcmM (A B : pcmType) (f:fmet A B) (m:monotonic (FMet.Pack (FMet.class f) f)) := fmonoMixin m.
Definition mk_fpcm (A B : pcmType) (f:fmet A B) (m:monotonic (FMet.Pack (FMet.class f) f)) :
   fpcm A B := Eval hnf in fpcmType (mk_fpcmM m).

Lemma mcomp_mono (A B C : pcmType) (f:fpcm B C) (g:fpcm A B) : monotonic (mcomp f g).
move => A B C f g x y l. simpl. apply: fmonotonic. by apply: fmonotonic.
Qed.

Definition pcomp (A B C : pcmType) (f:fpcm B C) (g:fpcm A B) : fpcm A C := Eval hnf in mk_fpcm (mcomp_mono f g).

Lemma mid_mono (A:pcmType) : monotonic (@mid A).
by move => A.
Qed.

Definition pid (A:pcmType) : fpcm A A := Eval hnf in mk_fpcm (@mid_mono A).

Lemma pcmMorphSetoidAxiom A B : @Setoid.axiom (fpcm A B) (fun f g => (f:metricCatType _ _) =-= g).
move => A B.
split ; last split.
by move => f.
by move => f g h ; apply: tset_trans.
by move => f g ; apply: tset_sym.
Qed.

Canonical Structure pcmMorphSetoidMixin A B := SetoidMixin (pcmMorphSetoidAxiom A B).
Canonical Structure pcmMorphSetoidType A B := Eval hnf in SetoidType (pcmMorphSetoidMixin A B).

Lemma pcmCatAxiom : @Category.axiom pcmType pcmMorphSetoidType (@pcomp) (@pid).
split ; last split ; last split.
by move => A B f x.
by move => A B f x.
by move => A B C D f g h x.
move => A B C f f' g g' e e' x. apply tset_trans with (y:=f (g' x)).
simpl in f. apply: (frespect f). by apply e'.
by apply e.
Qed.

Canonical Structure pcmCatMixin := CatMixin pcmCatAxiom.
Canonical Structure pcmCatType := Eval hnf in CatType pcmCatMixin.

Definition mk_fpcmX (A B : pcmType) (f:A -> B) (n:nonexpansive f) (m:monotonic f)
  : A =-> B := FPCM.Pack (FPCM.Class (FMet.Mixin n) (FMon.Mixin m)) f.

Section PROD.
Variable A B : pcmType.

Lemma prod_pcm_axiom : PreCBUmet.axiom (PreOrd.Ole (prod_ordMixin (PreCBUmet.ordType A) (PreCBUmet.ordType B))).
split.
- case => x0 x1. case => x0' x1'. case => y0 y1. case => y0' y1'. simpl. case => e0 e1. simpl in e0. simpl in e1.
  case => e2 e3. simpl in e2. simpl in e3. case => l l'.
  by split ; [apply (pcm_respect e0 e2 l) | apply (pcm_respect e1 e3 l')].
- move => c c' X. by split ; simpl ; apply pcm_chain_mono => i ; by [apply (proj1 (X i)) | apply (proj2 (X i))].
Qed.

Canonical Structure prod_pcmMixin := PCMMixin prod_pcm_axiom (pcm_getElem A,pcm_getElem B).
Canonical Structure prod_pcmType := Eval hnf in PCMType prod_pcmMixin.

Variable (C:pcmType) (f:C =-> A) (g:C =-> B).

Definition pprod_fun : C =-> prod_pcmType := Eval hnf in mk_fpcmX (Sprod_fun_ne f g) (Prod_fun_mono f g).
Definition pfst : prod_pcmType =-> A := Eval hnf in mk_fpcmX (@Sfst_ne _ _) (@fst_mon _ _).
Definition psnd : prod_pcmType =-> B := Eval hnf in mk_fpcmX (@Ssnd_ne _ _) (@snd_mon _ _).

End PROD.

Lemma pcomp_simpl (A B C : pcmType) (f:A =-> B) (g: B =-> C) x : (g << f) x = g (f x).
by [].
Qed.

Lemma pcmProdCatAxiom : CatProduct.axiom (@pfst) (@psnd) (@pprod_fun).
move => A B C f g ; split ; [split | move => h ; case => P Q].
- by move => x.
- by move => x.
move => x. specialize (P x). specialize (Q x). rewrite <- (pair_eq_compat P Q).
simpl. by case: (h x).
Qed.

Canonical Structure pcmProdCatMixin := prodCatMixin pcmProdCatAxiom.
Canonical Structure pcmProdCatType := Eval hnf in prodCatType pcmProdCatMixin.

Lemma fpcm_respect2 (M M':pcmType) n : setoid_respect2 (fun f g : fpcm M M' => (f:fmet _ _) = n = g).
move => M M' n. split.
- move => f g h e. split => E.
  + by apply (Mrel_trans (Msym (proj2 (Mrefl (g:fmet _ _) h) e n)) E).
  + by apply (Mrel_trans ((proj2 (Mrefl (g:fmet _ _) h) e n)) E).
- move => f g h e. split => E.
  + by apply (Mrel_trans E (proj2 (Mrefl (g : fmet _ _) h) e n)).
  + by apply (Mrel_trans E ((proj2 (Mrefl (h : fmet _ _) g) (tset_sym e) n))).
Qed.

Lemma fpcm_metric_axiom A B : Metric.axiom (fun n => (fun f g : fpcm A B => (f:fmet _ _) = n = g)).
move => A B n x y z. split ; last split ; last split ; last split ; clear.
- by apply: Mrefl.
- by apply: Msym.
- by apply: Mrel_trans.
- by apply: Mmono.
- by apply: Mbound.
Qed.

Canonical Structure fpcm_metricMixin (A B : pcmType) := MetricMixin (@fpcm_metric_axiom A B).
Canonical Structure fpcm_metricType (A B : pcmType) := Eval hnf in MetricType (@fpcm_metricMixin A B).

Lemma pcm_morph_nonexp A B : nonexpansive (fun f:fpcm_metricType A B => (f:(A:cmetricType) -=> B)).
move => A B n f g e x. by apply e.
Qed.

Definition PCM_morph (A B:pcmType) : (fpcm_metricType A B) =-> ((A:cmetricType) -=> B) :=
 Eval hnf in mk_fmet (@pcm_morph_nonexp A B).
Implicit Arguments PCM_morph [A B].

Lemma lub_mono A B (c:cchain (fpcm_metricType A B)) : monotonic (umet_complete (liftc PCM_morph c)).
move => A B c a a' L. simpl.
apply pcm_chain_mono => i. simpl. by apply: fmonotonic.
Qed.

Definition lub_pcm_morph A B (c:cchain (fpcm_metricType A B)) : fpcm_metricType A B := Eval hnf in mk_fpcm (lub_mono c).

Lemma fpcm_cmetric_axiom A B : CMetric.axiom (@lub_pcm_morph A B).
move => A B c. by apply (cumet_conv (liftc PCM_morph c)).
Qed.

Canonical Structure fpcm_cmetricMixin (A B : pcmType) := CMetricMixin (@fpcm_cmetric_axiom A B).
Canonical Structure fpcm_cmetricType (A B : pcmType) := Eval hnf in CMetricType (fpcm_cmetricMixin A B).

Lemma fpcm_ordAxiom A B : PreOrd.axiom (fun (x y : fpcm_cmetricType A B) => (x:fmono _ _) <= y).
move => A B x. split ; first by [].
by move => y z ; apply Ole_trans.
Qed.

Canonical Structure fpcm_ordMixin A B := OrdMixin (@fpcm_ordAxiom A B).
Canonical Structure fpcm_ordType A B := Eval hnf in OrdType (fpcm_ordMixin A B).

Lemma fpcm_axiom A B : @PreCBUmet.axiom (fpcm_cmetricType A B) (fun x y => x <= y).
move => A B. split.
- move => x x' y y'. simpl. move => e e' l a. specialize (l a). specialize (e a). specialize (e' a). by apply (pcm_respect e e' l).
- move => c c' X. move => a. apply Ole_trans with (umet_complete (chain_app (liftc PCM_morph c) a)) ; first by [].
  apply Ole_trans with (umet_complete (chain_app (liftc PCM_morph c') a)) ; last by [].
  apply pcm_chain_mono. move => i. simpl. by apply (X i).
Qed.

Definition pconst (T T':pcmType) (x:T') : T =-> T' := Eval hnf in mk_fpcmX (@sconst_ne T T' x) (const_mon x).

Canonical Structure fpcm_pcmMixin (A B : pcmType) := PCMMixin (@fpcm_axiom A B) (pconst A (pcm_getElem B)).
Canonical Structure fpcm_pcmType (A B : pcmType) := Eval hnf in PCMType (fpcm_pcmMixin A B).

Definition ppair (A B : pcmType) (x:A) := Eval hnf in mk_fpcmX (@mpair_ne A B x) (pair1_mon x).

Lemma pcurry_ne (A B C : pcmType) (f:A * B =-> C) : nonexpansive (fun x => f << ppair _ x).
move => A B C f n x x' e y. simpl. apply: fnonexpansive. by split.
Qed.

Definition pcurryN (A B C : pcmType) (f:A * B =-> C) : metricCatType A (fpcm_pcmType B C) := Eval hnf in mk_fmet (pcurry_ne f).

Lemma pcurry_mono (A B C : pcmType) (f:A * B =-> C) : monotonic (pcurryN f).
move => A B C f x y l z. simpl. apply: fmonotonic. by split.
Qed.

Definition pcurry (A B C : pcmType) (f:A * B =-> C) : A =-> (fpcm_pcmType B C) := Eval hnf in mk_fpcm (pcurry_mono f).

Lemma spev_ne (B A:pcmType) : nonexpansive (fun (p:(fpcm_pcmType B A) * B) => mev B A (fst p : fmet_metricType B A,snd p)).
move => B A n. case => f x. case => f' x'. case. simpl. move => X Y.
apply Mrel_trans with (y:=f x') ; first by apply: fnonexpansive.
by apply X.
Qed.

Definition mpev B A : metricCatType ((fpcm_pcmType B A) * B)  A := Eval hnf in mk_fmet (@spev_ne B A).

Lemma mpev_mono B A : monotonic (@mpev B A).
move => A B.
case. simpl. move => f a. case ; simpl => f' a'.
move => X. apply Ole_trans with (y:=f' a). by apply (proj1 X a).
apply: fmonotonic. by apply (proj2 X).
Qed.

Definition pev (B A :pcmType) : ((fpcm_pcmType B A) * B) =-> A := Eval hnf in mk_fpcm (@mpev_mono B A).

Lemma pcmExpAxiom : CatExp.axiom (@pev) (@pcurry).
move => A B C f. split.
- by case => a b.
- move => h X a b. specialize (X (a,b)). by apply X.
Qed.

Canonical Structure pcmExpCatMixin := expCatMixin pcmExpAxiom.
Canonical Structure pcmExpCatType := Eval hnf in expCatType pcmExpCatMixin.

Lemma pcompMP (A B C:pcmType) : nonexpansive (fun (fg:((B -=> C) * (A -=> B))) => @pcomp A B C (fst fg) (snd fg)).
move => A B C n. case => f g. case => f' g'. case. simpl => e e'.
move => x. apply Mrel_trans with (y:= f (g' x)) ; last by apply e. simpl.
apply: fnonexpansive. by apply e'.
Qed.

Definition pcompM (A B C:pcmType) : metricCatType ((B -=> C) * (A -=> B)) (A -=> C) := Eval hnf in mk_fmet (@pcompMP A B C).

Lemma pcomp_mono (A B C:pcmType) : monotonic (@pcompM A B C).
move => A B C. case => f g. case => f' g'. case. simpl. move => l l'.
move => x. simpl. apply Ole_trans with (y:=f (g' x)). apply: (fmonotonic f). by apply l'.
by apply l.
Qed.

Definition Pcomp A B C : ((B -=> C) * (A -=> B)) =-> A -=> C := Eval hnf in mk_fpcm (@pcomp_mono A B C).
Implicit Arguments Pcomp [A B C].

Lemma Pcomp_simpl A B C (f:B =-> C) (g:A =-> B) : (@Pcomp A B C (f,g)) = f << g.
by [].
Qed.

Lemma pev_simpl (D0 D1:pcmType) (f : D0 -=> D1) a : pev _ _ (f,a) = f a.
by [].
Qed.

Canonical Structure morphc_pcmType (A B:pcmType) := Eval hnf in @sub_cmetricType (morph_cmetricType A B) (@contractive _ _) (@contractive_complete A B).

Implicit Arguments morphc_pcmType [].

Definition morphc_morph A B (f:morphc_pcmType A B) := match f with exist f' _ => f' end.

Definition morphc_fun A B : (morphc_pcmType A B) -> A -> B := fun f x => match f with exist f' _ => f' x end.

Definition Fixp (M:pcmType) (f:morphc_pcmType M M) : M :=
match f with exist f c => fixp c (pcm_getElem M) end.

Lemma Fixp_nonexp (M:pcmType) : nonexpansive (fun f:morphc_pcmType M M => Fixp f).
move => M n f f' e. simpl. case: f e => f c. case: f' => f' c' e. simpl. apply: fixp_ne.
by apply e.
Qed.

Definition FIXPx (M:pcmType) : (morphc_pcmType M M) =-> M := Eval hnf in mk_fmet (@Fixp_nonexp M).

Definition FIXP (M:pcmType) : (morphc_pcmType M M) =-> M := locked (FIXPx M).

Implicit Arguments FIXP [M].

Lemma FIXP_fp (M:pcmType) (f:morphc_pcmType M M) : FIXP f =-= morphc_fun f (FIXP f).
move => M. case => f C. simpl. unlock FIXP. simpl.
apply: fixp_eq.
Qed.

Lemma discrete_pcm_axiom T : PreCBUmet.axiom (@Ole (discrete_ordType (discrete_cmetricType T))).
move => T. split.
- move => x x' y y'. simpl. unfold tset_eq. simpl. move => e0 e1 e2. rewrite <- e0. rewrite e2. by apply e1.
- move => c c'. simpl. move => X. by apply: X.
Qed.

Definition discrete_pcmMixin T (x:T) := PCMMixin (@discrete_pcm_axiom T) x.
Definition discrete_pcmType T x := Eval hnf in @PCMType (discrete_cmetricType T) (@discrete_pcmMixin T x).

Implicit Arguments discrete_pcmType [].

Section IProd.
Variable I : Type.
Variable P : I -> pcmType.

Lemma prodI_pcmAxiom : @PreCBUmet.axiom (prodI_cmetricType P) (PreOrd.Ole (prodI_ordMixin (fun x => PreCBUmet.ordType (P x)))).
split.
- move => x x' y y' e e'. simpl. move => X i. specialize (X i). specialize (e i). specialize (e' i).
  by apply (pcm_respect e e' X).
- move => x y X i. apply Ole_trans with (y:=umet_complete (liftc (mproj P i) x)) ; first by [].
  apply Ole_trans with (y:=umet_complete (liftc (mproj P i) y)) ; last by [].
  apply pcm_chain_mono => n. by apply (X n).
Qed.

Canonical Structure prodI_pcmMixin := PCMMixin prodI_pcmAxiom (fun i => pcm_getElem (P i)).
Canonical Structure prodI_pcmType := Eval hnf in @PCMType (prodI_cmetricType P) prodI_pcmMixin.

Lemma mproj_mono i : monotonic (mproj P i:metricCatType prodI_pcmType (P i)).
move => i x y e. by apply e.
Qed.

Definition pproj i : prodI_pcmType =-> P i := Eval hnf in mk_fpcm (mproj_mono i).

Variable C:pcmType.
Variable (f:forall i, C =-> P i).

Lemma mprodI_fun_mono : monotonic (mprodI_fun f:metricCatType C prodI_pcmType).
move => x y e i. by apply: (fmonotonic (f i)).
Qed.

Definition pprodI_fun : C =-> prodI_pcmType := Eval hnf in mk_fpcm mprodI_fun_mono.

End IProd.

Lemma pcmProdIAxiom : forall I:Type, @CatIProduct.axiom _ I (@prodI_pcmType I) (@pproj I) (@pprodI_fun I).
move => I A X f. split.
- by move => i x.
- move => m Z x i. simpl. specialize (Z i x). by apply Z.
Qed.

Canonical Structure pcmProdIMixin := prodICatMixin pcmProdIAxiom.
Canonical Structure pcmProdICat := Eval hnf in prodICatType pcmProdIMixin.

Lemma pprod_funS_ne (A B C:pcmType) : nonexpansive (fun (x:(A =-> B) * (A =-> C)) => pprod_fun (fst x) (snd x)).
move => A B C n. case => f g. case => f' g'. case => e0 e1 x. simpl.
specialize (e0 x). specialize (e1 x). by split.
Qed.

Definition pprod_fun_ne (A B C:pcmType) : metricCatType ((A -=> B) * (A -=> C)) (A -=> B * C) := Eval hnf in mk_fmet (@pprod_funS_ne A B C).

Lemma pprod_funN_mono (A B C:pcmType) : monotonic (@pprod_fun_ne A B C).
move => A B C.
case => f g. case => f' g'. case => l0 l1. move => x. simpl. specialize (l0 x). specialize (l1 x). by split.
Qed.

Definition Pprod_fun (A B C:pcmType) : ((A -=> B) * (A -=> C) =-> A -=> B * C) := Eval hnf in mk_fpcm (@pprod_funN_mono A B C).

Implicit Arguments Pprod_fun [A B C].
Implicit Arguments pprod_fun_ne [A B C].

Lemma unit_pcm_axiom : @PreCBUmet.axiom unit_cmetricType (@Ole _).
by [].
Qed.

Canonical Structure unit_pcmMixin := PCMMixin unit_pcm_axiom tt.
Canonical Structure unit_pcmType := Eval hnf in PCMType unit_pcmMixin.

Lemma pcmTerminalAxiom : CatTerminal.axiom unit_pcmType.
move => A f g.
by move => x.
Qed.

Canonical Structure pcmTerminalCatMixin := terminalCatMixin (fun X => pconst X tt) pcmTerminalAxiom.
Canonical Structure pcmTerminalCatType := Eval hnf in terminalCatType pcmTerminalCatMixin.

Lemma pid_simpl (T:pcmType) (x:T) : pid _ x = x.
by [].
Qed.

Section SubPCMetric.

Variable (M:pcmType) (P:M -> Prop) (C:@ccomplete M P).

Lemma sub_pcm_axiom : @PreCBUmet.axiom (sub_cmetricType C) (PreOrd.Ole (sub_ordMixin P)).
split.
- case => x Px. case => x' Px'. case => y Py. case => y' Py'. simpl. by apply: pcm_respect.
move => c c'; simpl => X. apply pcm_chain_mono => i. specialize (X i).
apply Ole_trans with (y:=mforget P (c i)) ; first by [].
apply Ole_trans with (y:=mforget P (c' i)) ; last by [].
move: X. case (c i) => x Px. by case: (c' i) => y Py e.
Qed.

Variable (x:M) (Px:P x).

Canonical Structure sub_pcmMixin := PreCBUmet.Mixin sub_pcm_axiom (exist (fun x => P x) x Px).
Canonical Structure sub_pcmType := Eval hnf in PCMType sub_pcmMixin.

Lemma mInheritFun_mono (N : pcmType) (f:N =-> M) (X:forall n, P (f n)) : monotonic (mInheritFun X:metricCatType N sub_pcmType).
move => N f X y y' e. by apply:fmonotonic.
Qed.

Definition pInheritFun (N : pcmType) (f:N =-> M) (X:forall n, P (f n)) : N =-> sub_pcmType :=
  Eval hnf in mk_fpcm (@mInheritFun_mono N f X).

Lemma mforget_mono : monotonic (mforget P:metricCatType sub_pcmType M).
case => y Py ; by case.
Qed.

Definition pforget : sub_pcmType =-> M := Eval hnf in mk_fpcm mforget_mono.

Lemma pforget_mono (N:pcmType) (f:N =-> sub_pcmType) g : pforget << f =-= pforget << g -> f =-= g.
move => N f g. apply: mForget_mono.
Qed.

End SubPCMetric.

Require Import MetricRec.

Canonical Structure pcmECatMixin := @CmetricECatMixin _ pcmTerminalCatMixin _ _ (@Pcomp) (fun X Y Z m m' => tset_refl _).
Canonical Structure pcmECatType := Eval hnf in CmetricECatType pcmECatMixin.

Section Limit.

Variable T:Tower pcmECatType.

Definition limit_cond := (fun p : prodI_pcmType (tobjects T) =>
      forall i : nat, tmorphisms T i (pproj (tobjects T) i.+1 p) =-= pproj (tobjects T) i p).

Lemma limit_ccomplete : ccomplete limit_cond.
unfold limit_cond.
move => c IH. simpl. simpl in IH.
move => i.
have A:=nonexp_continuous (tmorphisms T i << (pproj (tobjects T) i.+1)) c.
apply (tset_trans A). clear A. rewrite -> (nonexp_continuous (pproj (tobjects T) i) c).
apply: umet_complete_ext => j. simpl. specialize (IH j i). by apply IH.
Qed.

Lemma limit_ne : limit_cond (fun n => t_nm T 0 n (pcm_getElem (tobjects T O))).
move => n. have a:= (t_nmProjection T 0 n (pcm_getElem (tobjects T O))).
simpl. simpl in a. by apply (tset_sym a).
Qed.

Definition cbult_c : Cone T.
exists (sub_pcmType limit_ccomplete limit_ne) (fun i => pproj (tobjects T) i << pforget limit_ccomplete limit_ne).
move => i. simpl. case => y Py. simpl. by apply: Py.
Defined.

Lemma t_nmLimitCond i x : limit_cond (pprodI_fun (t_nm T i) x).
move => i x n.
apply tset_trans with (y:=(t_nm T i n) x) ; last by [].
apply tset_trans with (y:=tmorphisms T n (t_nm T i n.+1 x)) ; first by [].
apply (tset_sym (t_nmProjection T i n x)).
Qed.

Definition cbult_cc : CoCone T.
exists (sub_pcmType limit_ccomplete limit_ne) (fun i:nat => pInheritFun limit_ccomplete limit_ne (@t_nmLimitCond i)).
move => i. simpl. move => y n. by apply (tset_sym (t_nmEmbedding T i n y)).
Defined.

Lemma comp_chain_left (A B C:pcmType) (f:B =-> C) (c:cchain (@cmetricMorph pcmECatType A B)) :
   f << (umet_complete c) =-= umet_complete (liftc (exp_fun Pcomp f) c).
move => A B C f c. by rewrite <- nonexp_continuous.
Qed.

Lemma comp_chain_right (A B C:pcmType) (f:A =-> B) (c:cchain (@cmetricMorph pcmECatType B C)) :
   (umet_complete c) << f =-= umet_complete (liftc (exp_fun (Pcomp << <|pi2,pi1|>) f) c).
move => A B C f c. by rewrite <- nonexp_continuous.
Qed.

Lemma limit_id : umet_complete (chainPE cbult_cc cbult_c) =-= Id.
refine (pforget_mono _).
apply tset_trans with (y:= pprodI_fun (fun i => (pproj (tobjects T) i << pforget limit_ccomplete limit_ne))) ;
  last by apply tset_sym ; refine (mprodI_fun_unique _) ; move => i.
apply: prodi_unique.
move => i. rewrite -> comp_assoc.
rewrite -> comp_chain_left.
rewrite -> (cut_complete_eq i _).
apply tset_trans with (y:= @umet_complete ((sub_pcmType limit_ccomplete limit_ne) -=> tobjects T i) (const_cchain (pproj _ i << pforget limit_ccomplete limit_ne))) ;
  last by rewrite -> umet_complete_const.
apply: umet_complete_ext => n.
have a:= coneCom_l cbult_c (leq_addr n i). simpl.
by apply (tset_sym a).
Qed.

Definition cbult_l : Limit T.
exists cbult_c (fun c => umet_complete (chainPE cbult_cc c)).
- move => A n.
  rewrite -> comp_chain_left.
  rewrite -> (cut_complete_eq n).
  apply tset_trans with (y:=umet_complete (const_cchain (mcone A n))) ; first by rewrite -> umet_complete_const.
  apply: umet_complete_ext. move => i. apply tset_trans with (y:=t_nm T (n + i) n << (mcone A (n + i))) ; last by [].
  have a:= @coneCom_l _ _ A (n+i) n (leq_addr i n). by rewrite <- a.
- move => A h C. apply tset_trans with (y:=umet_complete  (chainPE cbult_cc cbult_c) << h) ;
     first by rewrite -> (limit_id).
  rewrite -> comp_chain_right.
  apply: umet_complete_ext. move => i. specialize (C i).
  apply tset_trans with (y:= (mcocone cbult_cc i << mcone cbult_c i) << h) ; first by [].
  apply tset_trans with (y:=(mcocone cbult_cc i << mcone A i)) ; last by [].
  rewrite <- comp_assoc. by rewrite -> C.
Defined.

End Limit.

Section DInf.

Variable F : BiFunctor pcmECatType.

Definition F_start : unit_pcmType =-> ob F unit_pcmType unit_pcmType := pconst One (pcm_getElem (ob F One One)).

Variable C : forall A B C D : pcmType, contractive (morph F A B C D).

Definition DInf := Eval hnf in @DInf _ cbult_l F F_start C.
Definition Fold : ob F DInf DInf =-> DInf := Fold cbult_l F_start C.
Definition Unfold : DInf =-> ob F DInf DInf := Unfold cbult_l F_start C.

Lemma FU_iso : Fold << Unfold =-= Id.
by apply (FU_id cbult_l F_start C).
Qed.

Lemma UF_iso : Unfold << Fold =-= Id.
by apply (UF_id cbult_l F_start C).
Qed.

End DInf.

Lemma BiArrow_morphS_ne (A B C D:pcmType) : nonexpansive (fun (p:@prod cmetricProdCatType ((B -=> A)) ((C -=> D))) => 
    @Category.comp pcmCatType _ _ _ (exp_fun (Pcomp << <|pi2,pi1|>) (pfst _ _ p)) (exp_fun (@Pcomp A C D) (psnd _ _ p))).
move => A B C D n.
case => f g. case => f' g' [e e'] h x. simpl.
refine (Mrel_trans (e' _) _). simpl. do 2 apply: fnonexpansive. by apply e.
Qed.

Definition BiArrow_morph (A B C D:pcmType) : ((@prod cmetricProdCatType (B -=> A) (C -=> D)) =-> (((A -=> C) -=> (B -=> D)):pcmType)) := Eval hnf in mk_fmet (@BiArrow_morphS_ne A B C D).

Lemma BiArrow_morph_simpl A B C D (f:B =-> A) (g:C =-> D) h : BiArrow_morph A B C D (f,g) h = g << h << f.
by [].
Qed.

Definition BiArrow : BiFunctor pcmECatType.
exists (fun A B => (A -=> B)) (BiArrow_morph).
by move => A B C D E F f g h k x y.
by move => A B h x.
Defined.

Definition BiComp (BF:BiFunctor pcmECatType) (BG:BiFunctor pcmECatType) (BH:BiFunctor pcmECatType) : BiFunctor pcmECatType.
move => BF BG BH.
exists (fun D E => ob BH (ob BF E D) (ob BG D E)) 
 (fun D E F G => ((morph BH (ob BF F D) (ob BF G E) (ob BG D F) (ob BG E G)) <<
           (mprod_fun ((morph BF G F E D) << <| psnd _ _, pfst _ _ |>) (morph BG D E F G)))).
- move => A B C D E F f g h k. simpl. rewrite -> (morph_comp BH).
  by rewrite -> (morph_eq_compat BH (morph_comp BF k h g f) (morph_comp BG f g h k)).
- move => A B. simpl.
  rewrite -> (morph_eq_compat BH (morph_id BF B A) (morph_id BG A B)).
  by rewrite morph_id.
Defined.

Lemma comp_BF_contractive (BF:BiFunctor pcmECatType) (BG:BiFunctor pcmECatType) A B C D :
   contractive (morph BF D C B A) -> contractive (morph BG A B C D) -> contractive (morph (BiComp BF BG BiArrow) A B C D).
move => BF BG A B C D X Y n. case => x0 x1. case => y0 y1. case => e0 e1.
move => h x. simpl.
apply Mrel_trans with (y:=morph BG A B C D (x0,x1) (h (morph BF _ _ _ _ (y1,y0) x))) ; last by apply: Y.
do 2 apply: fnonexpansive. by apply: X.
Qed.

Require Import Finmap.

Section FinDom.

Variable T : compType.

Section Ord.
Variable O:pcmType.

Lemma findom_ord_axiom : PreOrd.axiom (fun (f f' : FinDom T O) => forall t m, f t = Some m -> exists m', f' t = Some m' /\ m =-= m').
move => f ; split ; clear.
- move => t m E. exists m. by split.
- move => g h X Y t m E.
  specialize (X t m E). destruct X as [m' [E' L']]. specialize (Y t m' E'). destruct Y as [m0 [E0 L0]].
  exists m0 ; split ; first by []. by apply (tset_trans L' L0).
Qed.

End Ord.

Variable M:pcmType.
Lemma findom_pcm_axiom : @PreCBUmet.axiom (findom_cmetricType T M) (PreOrd.Ole (OrdMixin (@findom_ord_axiom M))).
split.
- move => x x' y y'. simpl. move => e e' X t m E. have A:=proj2 e t. rewrite E in A.
  specialize (X t).
  case: (x t) A X => m' ; last by []. move => E' A. specialize (A m' (refl_equal _)). destruct A as [m0 [E0 L0]].
  have B:=proj2 e' t. rewrite E0 in B. case: (y' t) B ; last by []. move => yt X. exists yt. split ; first by [].
  have Y:m0 =-= yt by apply X. rewrite <- Y. rewrite <- L0. by apply (tset_sym E').
- move => c c'. simpl. unfold umet_complete. simpl. unfold findom_lub.  move => X t m E.
  have D:t \in dom (findom_map (fun x (X:x \in dom (c 1)) => umet_complete (findom_chainx X))) by
    rewrite findom_indom ; rewrite E.
  rewrite <- dom_findom_map in D. have X':= X 1 t (indom_app D) (sym_eq (indom_app_eq D)).
  destruct X' as [m1 [E1 L]]. have D':t \in dom (c' 1) by rewrite findom_indom ; rewrite E1.
  rewrite -> (dom_findom_map (fun x (X:x \in dom (c' 1)) => umet_complete (findom_chainx X))) in D'.
  rewrite findom_indom in D'.
  case_eq (findom_map (fun x (X:x \in dom (c' 1)) => umet_complete (findom_chainx X)) t) ;
    last by move => e0 ; rewrite e0 in D'.
  move => m' e'. exists m'. rewrite e'. split ; first by []. rewrite -> (findom_map_app D) in E.
  rewrite <- findom_indom in D'. rewrite <- dom_findom_map in D'.
  rewrite -> (findom_map_app D') in e'. case: E. case: e'. move => E E'. rewrite <- E. rewrite <- E'.
  apply: (proj1 (Mrefl _ _)) => n.  clear m m' E E'.
  destruct (cumet_conv (findom_chainx D) n) as [m A].
  destruct (cumet_conv (findom_chainx D') n) as [m' A'].
  specialize (A (m+m')%N). specialize (A' (m+m')%N). rewrite leq_addr in A. rewrite leq_addl in A'.
  specialize (A is_true_true). specialize (A' is_true_true). refine (Mrel_trans _ A').
  apply (Mrel_trans (Msym A)). clear A A'. simpl. case: n ; first by []. move => n.
  have C:Some (indom_app (findom_chain_dom (m + m') D)) = n.+1 = Some (indom_app (findom_chain_dom (m + m') D')) ; last by apply C.
  do 2 rewrite indom_app_eq. specialize (X (m+m').+1 t). have LL:Some (indom_app D) =-= Some m1 by [].
  rewrite indom_app_eq in LL. clear L.
  case_eq (c (m+m').+1 t).
  + move => ct E. specialize (X _ E). destruct X as [ct' [X E']]. rewrite E. rewrite X. simpl.
    by apply: (proj2 (Mrefl _ _) E').
  + move => E. have Y:=findom_indom (c (m+m').+1) t. rewrite E in Y. simpl in Y.
    have A:=cchain_cauchy c. specialize (A 1 1 (m+m').+1 (ltnSn _) (ltn0Sn _)).
    have B:=proj1 A. have C:t \notin (dom (c 1)) by rewrite B ; apply negbFE ; rewrite Y.
    rewrite findom_indom in C. by case: (c 1 t) LL C.
Qed.

Canonical Structure findom_pcmMixin := PCMMixin findom_pcm_axiom (fdEmpty T M).
Canonical Structure findom_pcmType := Eval hnf in PCMType findom_pcmMixin.

End FinDom.

Section sspost.
Variable C:compType.
Variable T T':pcmType.

Lemma sspost1_ne (f:T =-> T') : nonexpansive (fun (p:findom_pcmType C T) => @post_comp C T T' (fun x => Some (f x)) p).
move => f n g g' e.
case: n e ; first by []. move => n e.
split.
- simpl. do 2 rewrite dom_post_compS. by apply (proj1 e).
- move => i I I'. have A:Some (indom_app I) = n.+1 = Some (indom_app I') ; last by apply A.
  do 2 rewrite indom_app_eq. simpl. do 2 rewrite post_comp_simpl.
  rewrite dom_post_compS in I'. rewrite dom_post_compS in I.
  have a:=proj2 e i I I'.
  have B:Some (indom_app I) = n.+1 = Some (indom_app I') ; first by apply a. clear a.
  do 2 rewrite indom_app_eq in B. rewrite findom_indom in I'. rewrite findom_indom in I.
  case: (g i) I B ; last by []. simpl. move => s _.
  case: (g' i) I' ; last by []. simpl. move => s' _ ee. by apply: fnonexpansive.
Qed.

Definition nspost1 f : metricCatType (findom_pcmType C T) (findom_pcmType C T')  := Eval hnf in mk_fmet (sspost1_ne f).

Lemma nspost1_mon (f:T =-> T') : monotonic (nspost1 f).
move => f g g' l x. simpl. move => m. do 2 rewrite post_comp_simpl.
specialize (l x). case: (g x) l ; last by [].
move => gx l. specialize (l gx (refl_equal _)). simpl. case. move => e. case: l => gx' [e0 e1].
rewrite e0. simpl. exists (f gx'). split ; first by []. rewrite <- e. by apply: frespect.
Qed.

Definition spost1 f := Eval hnf in mk_fpcm (@nspost1_mon f).

Lemma spost_comp_ne : nonexpansive spost1.
case ; first by [].
move => n f f' e g. split ; first by simpl ; do 2 rewrite dom_post_compS.
move => i I I'. have A:Some (indom_app I) = n.+1 = Some (indom_app I') ; last by apply A.
do 2 rewrite indom_app_eq. simpl. do 2 rewrite post_comp_simpl.
simpl in I,I'. rewrite findom_indom in I. rewrite findom_indom in I'.
rewrite post_comp_simpl in I.
rewrite post_comp_simpl in I'. case: (g i) I I' ; last by [].
simpl. move => s _ _. specialize (e s). by apply e.
Qed.

Definition ppost_comp : metricCatType (T -=> T') _ := Eval hnf in mk_fmet spost_comp_ne.

End sspost.

Section BiFunc.

Variable BF:BiFunctor pcmECatType.
Variable Ct:compType.

Definition findomBF : BiFunctor pcmECatType.
exists (fun A B => findom_pcmType Ct (ob BF A B))
       (fun A B C D => @Category.comp metricCatType _ _ _ (ppost_comp Ct _ _) (morph BF A B C D)).
- move => A B C D E F f g h k. simpl. move => x. simpl.
  split ; first by do 3 rewrite dom_post_compS.
  move => t. do 3 rewrite post_comp_simpl. simpl. simpl in x. case (x t) ; last by [].
  move => xt. simpl. unfold tset_eq. simpl. by apply: (morph_comp BF).
- move => A B x. simpl. split ; first by rewrite dom_post_compS.
  move => t. rewrite post_comp_simpl. simpl in x. case: (x t) ; last by []. move => s. simpl. by apply: (morph_id BF).
Defined.

Lemma findom_BF_contractive A B C D : contractive (morph BF A B C D) -> contractive (morph findomBF A B C D).
move => A B C D X n. case => f g. case => f' g'. case => e0 e1. move => x.
split ; first by simpl ; do 2 rewrite dom_post_compS.
move => i I I'. have Y:Some (indom_app I) = n.+1 = Some (indom_app I') ; last by apply Y.
do 2 rewrite indom_app_eq. do 2 rewrite post_comp_simpl. rewrite dom_post_compS in I. rewrite -> findom_indom in I.
clear I'. simpl in I. case: (x i) I ; last by []. move => xi _. simpl.
specialize (X n (f,g) (f',g')). apply: X. by split.
Qed.

End BiFunc.

Lemma halve_respect2 (M:metricType) n : setoid_respect2 (fun x y : M => match n with O => True | S n' => x = n' = y end).
move => M n ; split => z x y e; case:n ;  [by [] | move => n | by [] | move => n] ; split => E.
- by apply (Mrel_trans (Msym (proj2 (Mrefl _ _) e n)) E).
- by apply (Mrel_trans ((proj2 (Mrefl _ _) e n)) E).
- by apply (Mrel_trans E (proj2 (Mrefl _ _) e n)).
- by apply (Mrel_trans E ((proj2 (Mrefl _ _) (tset_sym e) n))).
Qed.

Lemma halve_metric_axiom (M:metricType) : Metric.axiom (fun n => (fun x y : M => match n with O => True | S n' => x = n' = y end)).
move => M n x y z ; split ; last split ; last split ; last split ; simpl ; clear.
- split => X.
  + apply (proj1 (Mrefl x y)) => i. by apply (X (i.+1)).
  + case ; first by []. simpl. move => i. by apply (proj2 (Mrefl _ _) X i).
- move => X. case: n X ; first by []. simpl. move => n. by apply Msym.
- case: n ; first by move => a b.
  move => n. by apply: Mrel_trans.
- case: n ; first by []. move => n. by apply: Mmono.
- by [].
Qed.

Definition halve_metricMixin M := MetricMixin (@halve_metric_axiom M).
Definition halve_metricType (M:metricType) := Eval hnf in @MetricType M (@halve_metricMixin M).

Definition halve_chain (M:metricType) (c:cchain (halve_metricType M)) : cchain M.
move => M c. exists (fun i => c i.+1:M).
move => n i j L L'. simpl. have C:=cchain_cauchy c. by apply (C n.+1 i.+1 j.+1 L L').
Defined.

Lemma halve_cmetric_axiom (M:cmetricType) : CMetric.axiom (fun c : cchain (halve_metricType M) => (@umet_complete M (halve_chain c))).
move => M c n. case: n ; first by exists O. move => n. simpl.
destruct (cumet_conv (halve_chain c) n) as [m X].
exists m.+1. case ; first by [].
move => i L. by apply (X i L).
Qed.

Definition halve_cmetricMixin M := CMetricMixin (@halve_cmetric_axiom M).
Definition halve_cmetricType (M:cmetricType) := Eval hnf in @CMetricType (@halve_metricType M) (@halve_cmetricMixin M).

Lemma halve_ord_axiom (P:pcmType) : PreOrd.axiom (fun a b : halve_cmetricType P => a <= b).
move => O x. split ; first by []. by move => y z ; apply Ole_trans.
Qed.

Lemma halve_pcm_axiom (P:pcmType) : PreCBUmet.axiom (PreOrd.Ole (OrdMixin (@halve_ord_axiom P))).
move => P. split.
- move => x x' y y'. simpl. by apply: (pcm_respect).
- move => c n  C. simpl. simpl in C. apply: pcm_chain_mono => i. simpl. by apply C.
Qed.

Definition halve_pcmMixin P := PCMMixin (@halve_pcm_axiom P) (pcm_getElem P).
Definition halve_pcmType (P:pcmType) := Eval hnf in @PCMType (halve_cmetricType P) (@halve_pcmMixin P).

Section halve_BF.

Variable T:pcmType.

Variable BF:BiFunctor pcmECatType.

Lemma halve_morph_ne (A B:pcmType) : nonexpansive (fun (p : (A -=> B) * halve_pcmType A) => fst p (snd p) : halve_pcmType B).
move => A B. case ; first by [].
move => n. case ; simpl => f x. case ; simpl => f' x'.
case => e e'. specialize (e x).
apply: (Mrel_trans (Mrel_mono (leqW (leqnn n)) e)). by apply: fnonexpansive.
Qed.

Definition halve_morphN A B : metricCatType ((A -=> B) * (halve_pcmType A)) (halve_pcmType B) := Eval hnf in mk_fmet (@halve_morph_ne A B).

Lemma halve_morphP (A B:pcmType) : monotonic (@halve_morphN A B).
move => A B. case ; simpl => f x. case => f' x'. simpl. case. simpl => l l'.
specialize (l x). simpl in l. rewrite -> l. by apply: fmonotonic.
Qed.

Definition halve_morphX A B : ((A -=> B) * (halve_pcmType A)) =-> halve_pcmType B := Eval hnf in mk_fpcm (@halve_morphP A B).

Definition halve_morph A B := exp_fun (@halve_morphX A B).

Definition halveBF : BiFunctor pcmECatType.
exists (fun A B => halve_pcmType (ob BF A B)) (fun A B C D => @Category.comp metricCatType _ _ _ (halve_morph _ _) (morph BF A B C D)).
- move => A B C D E F f g h k x. simpl. by apply (morph_comp BF f g h k x).
- move => A B x. simpl. by apply: (morph_id BF).
Defined.

Lemma halve_morph_contractive A B C D: contractive (morph halveBF A B C D).
move => A B C D n f g e x. simpl. by apply: (fnonexpansive (morph BF A B C D) e).
Qed.

End halve_BF.

Section Upred.

Variable T:Type.

(*=downclosed *)
Definition downclosed (p:nat * T -> Prop) := forall n k t, k < n -> p (n,t) -> p (k,t).
(*=End *)
Definition upred_fun (P:{p:nat * T -> Prop | downclosed p}) : nat * T -> Prop := fun x => let (f,_) := P in f x.

Lemma upred_downclosed (u:{p:nat * T -> Prop | downclosed p}) k k' t : (k <= k')%N -> upred_fun u (k',t) -> upred_fun u (k,t).
move => u k k' t. case_eq (k == k') => E. rewrite (eqP E). move => _. by apply id.
move => l. rewrite leq_eqVlt in l. rewrite E in l. simpl in l.
case: u => u P. simpl. by apply P.
Qed.

Lemma upred_setoid_axiom : Setoid.axiom (fun a b : {p:nat * T -> Prop | downclosed p} => forall p, (upred_fun a p <-> upred_fun b p)).
split ; last split ; first by case.
- case => x Px ; case => y Py ; case => z Pz X Y p. specialize (X p). specialize (Y p). by apply (iff_trans X Y).
- case => x Px ; case => y Py X p. specialize (X p). by rewrite X.
Qed.

Canonical Structure upred_setoidMixin := SetoidMixin upred_setoid_axiom.
Canonical Structure upred_setoidType := Eval hnf in SetoidType upred_setoidMixin.

Lemma upred_ext (a b:upred_setoidType) : (forall p, upred_fun a p <-> upred_fun b p) -> a =-= b.
case => a Pa. case => b Pb. simpl. move => X. by apply: X.
Qed.

Lemma upred_metric_axiom : Metric.axiom (fun n => (fun a b : upred_setoidType =>
        forall k t, k < n -> (upred_fun a (k,t) <-> upred_fun b (k,t)))).
move => n x y z ; split ; last split ; last split ; last split ; clear.
- split => X.
  + apply upred_ext ; case => k t. by specialize (X k.+1 k t (ltnSn _)).
  + move => n. move => k v l. by apply X.
- move => X ; simpl => k t l. by rewrite (X k t l).
- move => X Y ; simpl => k t l. rewrite (X k t l). by rewrite (Y k t l).
- move => X ; simpl => k t l. by apply (X k t (ltnW l)).
- by [].
Qed.

Canonical Structure upred_metricMixin := MetricMixin upred_metric_axiom.
Canonical Structure upred_metricType := Eval hnf in @MetricType upred_setoidType upred_metricMixin.

Lemma upred_comp_down (c:cchain upred_metricType) : downclosed (fun p => upred_fun (c (fst p).+1) p).
move => c n k t L X. simpl. simpl in X.
have C:=cchain_cauchy c. specialize (C k.+1 n.+1 k.+1 (ltnW L) (ltnSn _)).
case: (c n.+1) X C => cn Dcn. case: (c k.+1) => ck Dck ; simpl => X. unfold Mrel. simpl => Y.
specialize (Dcn _ _ t L X). specialize (Y k t (ltnSn _)). rewrite <- Y. by apply Dcn.
Qed.

Lemma upred_comp_axiom (c:cchain upred_metricType) : mconverge c (exist downclosed _ (@upred_comp_down c)).
move => c n. exists n. move => i L. move => k v l. simpl.
have A:=cchain_cauchy c. specialize (A k.+1 k.+1 i (ltnSn _) (ssrnat.leq_trans l L) k v (ltnSn _)).
by rewrite A.
Qed.

Canonical Structure upred_cmetricMixin := CMetricMixin upred_comp_axiom.
Canonical Structure upred_cmetricType := Eval hnf in @CMetricType upred_metricType upred_cmetricMixin.

Definition upred_less (x y : upred_cmetricType) : Prop := forall p, upred_fun x p -> upred_fun y p.

Lemma upred_ord_axiom : PreOrd.axiom upred_less.
move => x ; split ; clear ; first by case.
move => y z X Y. case => k t A. specialize (X (k,t) A). by specialize (Y (k,t) X).
Qed.

Lemma upred_pcm_axiom : @PreCBUmet.axiom upred_cmetricType (PreOrd.Ole (OrdMixin upred_ord_axiom)).
split.
- move => x x'. simpl. move => y y' e e'. move => X. case => k t Y. specialize (X (k,t)). specialize (e (k,t)).
  specialize (e' (k,t)). rewrite <- e'. apply X. rewrite e. by apply Y.
- move => c c'. simpl. move => X. case => k t. simpl. by apply (X k.+1).
Qed.

Definition upredEmptyP : upred_cmetricType.
exists (fun x => False). by [].
Defined.

Canonical Structure upred_pcmMixin := PCMMixin upred_pcm_axiom upredEmptyP.
Canonical Structure upred_pcmType := Eval hnf in @PCMType upred_cmetricType upred_pcmMixin.

Definition upred_empty : upred_pcmType := upredEmptyP.

End Upred.

Definition constBF (T:pcmType) : BiFunctor pcmECatType.
move => T. exists (fun (A B:pcmType) => T) (fun (A B C D:pcmType) => mconst ((B -=> A) * (C -=> D)) (@pid T)).
by move => A B C D E F f g h k x.
by move => A B x.
Defined.

Lemma constBF_contractive (T A B C D:pcmType) : contractive (morph (constBF T) A B C D).
move => T A B C D n x y e a. simpl. by apply (proj2 (Mrefl _ _)).
Qed.

Section Product.
Variable BF BG:BiFunctor pcmECatType.

Section Map.
Variable A B C D : pcmType.

Lemma mprod_mapP : nonexpansive (fun (p:(A =-> B) * (C =-> D)) => <| fst p << pi1, snd p << pi2|>).
move => n x y. case => e0 e1. case => z0 z1. split ; by [apply: e0 | apply: e1].
Qed.

Definition mpprod_map : metricCatType ((A -=> B) * (C -=> D))  (A * C -=> B * D) := Eval hnf in mk_fmet mprod_mapP.

Lemma Pprod_mapP : monotonic mpprod_map.
case => x0 x1. case => y0 y1. case ; simpl => l0 l1. case => z0 z1. simpl. split ; simpl ; by [apply l0 | apply l1].
Qed.

Definition Fprod_map : (A -=> B) * (C -=> D) =-> (A * C -=> B * D) := Eval hnf in mk_fpcm Pprod_mapP.

End Map.

Definition prod_BF : BiFunctor pcmECatType.
exists (fun A B => (ob BF A B) * (ob BG A B)) (fun (A B C D:pcmType) => (((Fprod_map (ob BF A C) (ob BF B D) (ob BG A C) (ob BG B D)) : cmetricCatType _ _) << (<|morph BF A B C D, morph BG A B C D|>))).
- move => A B C D E F f g h k. simpl. rewrite prod_map_prod_fun.
  do 2 rewrite comp_assoc. rewrite -> (morph_comp BF). by rewrite -> (morph_comp BG).
- move => A B. simpl. do 2 rewrite morph_id. do 2 rewrite comp_idL.
  by apply: prod_unique ; [rewrite prod_fun_fst | rewrite prod_fun_snd] ; rewrite comp_idR.
Defined.

Lemma prod_BF_contractive A B C D : contractive (morph BF A B C D) -> contractive (morph BG A B C D) ->
                                    contractive (morph prod_BF A B C D).
move => A B C D X Y n. case => x0 x1. case => y0 y1. case => e0 e1. case => z0 z1.
simpl. split. by apply: X. by apply: Y.
Qed.

End Product.

Definition idBF : BiFunctor pcmECatType.
exists (fun A B => B) (fun A B C D => msnd _ _).
by move => A B C D E F f g h k x.
by move => A B x.
Defined.

Close Scope O_scope.
Close Scope M_scope.
Close Scope C_scope.

