(**********************************************************************************
 * PredomCore.v                                                                   *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * July 2010                                                                      *
 * Build with Coq 8.2pl1 plus SSREFLECT                                           *
 **********************************************************************************)

(* new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(* endof new in 8.4 *)

From mathcomp Require Export ssreflect ssrnat ssrbool eqtype.
Require Export Categories.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** printing -c> %\cont% *)
(** printing -m> %\mon% *)

(** printing O1 %\ensuremath{O_1}% *)
(** printing O2 %\ensuremath{O_2}% *)
(** printing O3 %\ensuremath{O_3}% *)
(** printing O4 %\ensuremath{O_4}% *)
(** printing D1 %\ensuremath{D_1}% *)
(** printing D2 %\ensuremath{D_2}% *)
(** printing D3 %\ensuremath{D_3}% *)
(** printing x1 %\ensuremath{x_1}% *)
(** printing x2 %\ensuremath{x_2}% *)
(** printing x3 %\ensuremath{x_3}% *)
(** printing y1 %\ensuremath{y_1}% *)
(** printing y2 %\ensuremath{y_2}% *)
(** printing y3 %\ensuremath{y_3}% *)
(** printing p1 %\ensuremath{p_1}% *)
(** printing p2 %\ensuremath{p_2}% *)
(** printing p3 %\ensuremath{p_3}% *)

(** printing natO %nat0% *)
(** printing nat %nat% *)
(** printing lub %\ensuremath{\bigsqcup}% *)
(** printing cpo %cpo% *)
(** printing ord %ord% *)

(** ** Ordered type *)

(*=Ole *)
Module PreOrd.
  Definition axiom T (Ole : T -> T -> Prop) := 
    forall x , Ole x x /\ forall y z, (Ole x y -> Ole y z -> Ole x z).
  Record mixin_of T := Mixin {Ole : T -> T -> Prop; _ : axiom Ole}.
  Notation class_of := mixin_of (only parsing).
  Lemma setAxiom T (c:mixin_of T):Setoid.axiom (fun x y =>  Ole c x y /\ Ole c y x). (*CLEAR*)
Proof.
move => T.
case => le A. split ; last split.
- move => x. by split ; apply (proj1 (A x)).
- move => x y z. simpl. case => l0 l1. case => l2 l3.
  by split ; [apply (proj2 (A x) y z l0 l2) | apply (proj2 (A z) y x l3 l1)].
- move => x y. simpl. case => l0 l1. by split.
Qed.

(*CLEARED*)  Coercion base2 T (c:class_of T) : Setoid.class_of T := Setoid.Mixin (setAxiom c). 
  Structure type := Pack {sort :> Type; _ : class_of sort; _ : Type}. 
  Definition class cT := let: Pack _ c _ := cT return class_of cT in c. (*CLEAR*)
  Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
    let: Pack T c _ := cT return K _ (class cT) in k _ c.
  Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.
  Definition pack T c := @Pack T c T.
(* Definition pack T c := @Pack T (Class c) T. *)
 (*CLEARED*)
  Coercion setoidType (cT:type) := Setoid.Pack (class cT) cT.
End PreOrd.
Notation ordType := PreOrd.type.
Notation OrdMixin := PreOrd.Mixin.
Notation OrdType := PreOrd.pack.
Canonical Structure PreOrd.setoidType.
(*=End *)


Definition Ole := (fun (O:ordType) => PreOrd.Ole (PreOrd.class O)).
Implicit Arguments Ole [O].

Lemma Ole_refl (O:ordType) (x:O) : Ole x x.
unfold Ole. case. simpl. move => O. case.
move => le A _ x. by apply (proj1 (A x)).
Qed.

Lemma Ole_trans (O:ordType) (x y z:O) : Ole x y -> Ole y z -> Ole x z.
case. simpl. move => O. case.
move => le A T x y z L L'.
by apply (proj2 (A x) y z L L').
Qed.

Hint Resolve Ole_refl Ole_trans.

(*Hint Extern 2  (Ole (o:=?X1) ?X2 ?X3 ) => simpl Ole.*)

Bind Scope O_scope with PreOrd.sort.
Delimit Scope O_scope with PreOrd.

(** printing <= %\ensuremath{\sqsubseteq}% *)
Infix "<=" := Ole : O_scope.
Open Scope O_scope.

Arguments Scope Ole [O_scope _ _].

(*=Pointed *)
Module Pointed.
  Definition axiom (T:ordType) (l:T) := forall x, l <= x.
  Record mixin_of (T:ordType) := Mixin {least_elem : T; _ : axiom least_elem}. (*CLEAR*)

  Lemma leastP (T:ordType) (X:mixin_of T) : forall x, (least_elem X) <= x.
  move => T; case. simpl. move => l A x. by apply A.
  Qed.
  (*CLEARED*)
  Record class_of T := Class 
   { base :> PreOrd.class_of T; ext :> mixin_of (PreOrd.Pack base T)}. (*CLEAR*)

  Structure type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
  Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
  Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
    let: Pack T c _ := cT return K _ (class cT) in k _ c.
  Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.
  Definition pack := let k T c m := Pack (@Class T c m) T in PreOrd.unpack k.
  (*CLEARED*)
  Coercion ordType cT := PreOrd.Pack (class cT) cT.
  Definition setoidType cT := Setoid.Pack (class cT) cT. 
  Definition least cT := least_elem (class cT). (*CLEAR*)
  Implicit Arguments least [cT].
(*CLEARED*)
End Pointed. (*CLEAR*)

Notation pointedType := Pointed.type.
Notation PointedMixin := Pointed.Mixin.
Notation PointedType := Pointed.pack.
(*CLEARED*)
Notation PBot := Pointed.least.
Canonical Structure Pointed.ordType.
Canonical Structure Pointed.setoidType.
Lemma leastP (O:pointedType) (x:O) : PBot <= x. (*CLEAR*)
move => O x. by apply Pointed.leastP.
Qed.
(*CLEARED*)
(*=End *)

Lemma discrete_ordAxiom T : PreOrd.axiom (fun (x y : T) => x = y).
move => T a. split ; first by [].
by move => y z ; apply trans_eq.
Qed.

Canonical Structure discrete_ordMixin T := OrdMixin (@discrete_ordAxiom T).
Definition discrete_ordType T := Eval hnf in OrdType (discrete_ordMixin T).

Lemma Ole_refl_eq : forall  (O:ordType) (x y:O), x = y -> x <= y.
intros O x y H; rewrite H; auto.
Qed.

Hint Resolve Ole_refl_eq.

Lemma Ole_antisym : forall (O:ordType) (x y:O), x <= y -> y <= x -> x =-= y.
unfold Ole. unfold tset_eq. simpl.
case. move => T. case. simpl. move => X Y x y l0 l1. by split.
Qed.
Hint Immediate Ole_antisym.

Definition Oeq_refl (O:ordType) := @tset_refl O.

Hint Resolve Oeq_refl.

Lemma Oeq_refl_eq : forall (O:ordType) (x y:O), x=y -> x =-= y.
intros O x y H; rewrite H; auto.
Qed.
Hint Resolve Oeq_refl_eq.

Lemma Oeq_sym : forall (O:ordType) (x y:O), x =-= y -> y =-= x.
move => O x y X. by apply: tset_sym.
Qed.

Lemma Oeq_le : forall (O:ordType) (x y:O), x =-= y -> x <= y.
move => O. move => x y. case. move => A B. by apply A.
Qed.

Lemma Oeq_le_sym : forall (O:ordType) (x y:O), x =-= y -> y <= x.
move => O. move => x y. case. move => A B. by apply B.
Qed.

Hint Resolve Oeq_le.
Hint Immediate Oeq_sym Oeq_le_sym.

Lemma Oeq_trans : forall (O:ordType) (x y z:O), x =-= y -> y =-= z -> x =-= z.
move => O. apply (@tset_trans O).
Qed.
Hint Resolve Oeq_trans.

(** *** Setoid relations *)

Add Parametric Relation (O:ordType) : O (@tset_eq O : O -> O -> Prop)
       reflexivity proved by (@Oeq_refl O) symmetry proved by (@Oeq_sym O)
       transitivity proved by (@Oeq_trans O) as Oeq_Relation.

Add Parametric Relation (O:ordType) : O (@Ole O)
       reflexivity proved by (@Ole_refl O) 
       transitivity proved by (@Ole_trans O) as Ole_Relation.

Instance Oeq_sub_ord_morpoh_eq (D:ordType) : subrelation (@tset_eq D : D -> D -> Prop) (@Ole D).
move => D d d' x. by apply (proj1 x).
Qed.

Add Parametric Morphism (O:ordType) : (@Ole O)
 with signature (@tset_eq O : O -> O -> Prop) ==> (@tset_eq O : O -> O -> Prop) ==> iff as Ole_eq_compat_iff.
split; intuition.
apply Ole_trans with x; firstorder using Ole_trans.
apply Ole_trans with y.
firstorder.
apply Ole_trans with y0.
assumption.
intuition.
Qed.

Lemma Ole_eq_compat : 
     forall (O : ordType) (x1 x2 : O),
       x1 =-= x2 -> forall x3 x4 : O, x3 =-= x4 -> x1 <= x3 -> x2 <= x4.
move => O x1 x2 e x3 x4 e'. rewrite -> e. by rewrite -> e'.
Qed.

Lemma Ole_eq_right : forall (O : ordType) (x y z: O),
             x <= y -> y =-= z -> x <= z.
move => O x y z l e. rewrite l. by rewrite e.
Qed.

Lemma Ole_eq_left : forall (O : ordType) (x y z: O),
             x =-= y -> y <= z -> x <= z.
move => O x y z e l. rewrite e. by rewrite l.
Qed.

(** ** Monotonicity *)

(** *** Definition and properties *)

(*=monotonic *)
Definition monotonic (O1 O2 : ordType) (f : O1->O2) := forall x y, x <= y -> f x <= f y.
Module FMon. Section fmon.
 Variable O1 O2 : ordType.
 Record mixin_of (f:O1 -> O2) := Mixin { ext :> monotonic f}. (*CLEAR*)
 Notation class_of := mixin_of (only parsing).
(*CLEARED*)
 Structure type : Type := Pack {sort :> O1 -> O2; _ : class_of sort; _ : O1 -> O2}. (*CLEAR*)
 Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
 Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
   let: Pack T c _ := cT return K _ (class cT) in k _ c.
 Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.
 Definition pack f (c:class_of f) := @Pack f c f.
(*CLEARED*)End fmon. End FMon.
Notation fmono := FMon.type. (*CLEAR*)
Notation fmonoMixin := FMon.Mixin.
Notation fmonoType := FMon.pack. (*CLEARED*)
(*=End *)

Lemma fmonotonic O1 O2 (f:fmono O1 O2) : monotonic f.
move => O1 O2. case. simpl. move => f. by case.
Qed.

Hint Resolve fmonotonic.
Hint Unfold monotonic.

Definition stable (O1 O2:ordType) (f : O1 -> O2) := forall x y, x =-= y -> f x =-= f y.
Hint Unfold stable.

Lemma monotonic_stable : forall (O1 O2 : ordType) (f:O1 -> O2), 
             monotonic f -> stable f.
unfold monotonic, stable. move => O0 O1 f X x y e. split ; apply X ; by case e.
Qed.
Hint Resolve monotonic_stable.

(*=fmonoOrd *)
Lemma fmono_axiom (O1 O2:ordType) :
    PreOrd.axiom (fun f g:fmono O1 O2 => forall x, f x <= g x). (*CLEAR*)
Proof.
move => O1 O2 x. split ; first by [].
move => y z L L' e ; by apply (Ole_trans (L e) (L' e)).
Qed.
(*CLEARED*)
Canonical Structure fmono_ordMixin (T T':ordType) := OrdMixin (@fmono_axiom T T').
Canonical Structure fmono_ordType T T' :=
                              Eval hnf in OrdType (fmono_ordMixin T T').
(*=End *)

(* fmon <= *)
Definition fmon_less (A B: ordType): relation (fmono A B) := (@Ole (@fmono_ordType A B)).

Lemma fmon_less_preorder (A B: ordType): PreOrder (@fmon_less A B).
intros. split. red; intros. by apply Ole_refl.
red; intros x y z. by apply Ole_trans.
Qed.

Existing Instance fmon_less_preorder.

Add Parametric Morphism (A B : ordType) :
  (@FMon.sort A B) with signature (@fmon_less A B ==> @Ole A ==> @Ole B)
 as fmon_le_compat.
intros. apply Ole_trans with (y x0) ; first by auto.
by apply (fmonotonic y).
Qed.

(* fmon == *)
Definition fmon_equal (A B: ordType): relation (fmono A B) := (@tset_eq (@fmono_ordType A B)).

Lemma fmon_equal_equivalence (A B: ordType): Equivalence (@fmon_equal A B).
intros. split. intros x. by apply Oeq_refl.
intros x y E. split ; first by apply (Oeq_sym E). by apply E.
intros x y z E0 E1. by apply (Oeq_trans E0 E1).
Qed.

Existing Instance fmon_equal_equivalence.

Add Parametric Morphism (A B : ordType) :
  (@FMon.sort A B) with signature (@fmon_equal A B ==> @tset_eq A ==> @tset_eq B)
 as fmon_eq_compat.
move => f g fg x y xy. apply Oeq_trans with (g x) ; first by split ; [apply (proj1 fg) | apply (proj2 fg)].
by apply (monotonic_stable (fmonotonic g)).
Qed.

Lemma id_mon (O:ordType) : @monotonic O O id.
by move => O x y.
Qed.

Definition oidM (O:ordType) := fmonoMixin (@id_mon O).
Definition oid (O:ordType) := Eval hnf in  FMon.pack (oidM O).

Lemma ordMorphSetoidAxiom (O0 O1:ordType) : @Setoid.axiom (fmono O0 O1) (@tset_eq (fmono_ordType O0 O1)).
move => O1 O2. split ; first by []. split.
- by apply: Oeq_trans.
- by apply: Oeq_sym.
Qed.

Canonical Structure ordMorphSetoidMixin O0 O1 := SetoidMixin (ordMorphSetoidAxiom O0 O1).
Canonical Structure ordMorphSetoidType O0 O1 := Eval hnf in SetoidType (ordMorphSetoidMixin O0 O1).

Lemma comp_mon (O1 O2 O3:ordType) (f:fmono O2 O3) (g:fmono O1 O2) : monotonic (fun x => f (g x)).
move => O1 O2 O3 f g x y l.
by do 2 apply fmonotonic.
Qed.

Definition ocompM (O1 O2 O3:ordType) (f:fmono O2 O3) (g:fmono O1 O2) := fmonoMixin (comp_mon f g).
Definition ocomp (O1 O2 O3:ordType) (f:fmono O2 O3) (g:fmono O1 O2) := Eval hnf in fmonoType (ocompM f g).

Lemma ordCatAxiom : Category.axiom ocomp oid.
split ; first by move => O0 O1 f ; split.
split ; first by move => O0 O1 f ; split.
split ; first by move => O0 O1 O2 O3 f g h ; split.
move => O0 O1 O2 f f' g g' e e' ; split => x ; apply Ole_trans with (y:=f (g' x)).
- simpl. apply fmonotonic. by apply (proj1 e').
- simpl. by apply (proj1 e).
- simpl. by apply (proj2 e).
- simpl. apply fmonotonic. by apply (proj2 e').
Qed.

Canonical Structure ordCatMixin := CatMixin ordCatAxiom.
Canonical Structure ordCatType := Eval hnf in CatType ordCatMixin.

Open Scope C_scope.

Lemma fmon_stable : forall (O1 O2 : ordType) (f:O1 =-> O2), stable f.
intros; apply monotonic_stable; auto.
Qed.
Hint Resolve fmon_stable.

Definition mk_fmonoM (O1 O2:ordType) (f:O1 -> O2) (m:monotonic f) := fmonoMixin m.
Definition mk_fmono (O1 O2:ordType) (f:O1 -> O2) (m:monotonic f) : fmono O1 O2 := Eval hnf in fmonoType (mk_fmonoM m).

Section ordCatProd.

Variable O1 O2 : ordType.

Lemma prod_ord_axiom : PreOrd.axiom (fun x y :O1 * O2 => fst x <= fst y /\ snd x <= snd y).
move => x ; split ; clear ; first by case: x.
move => y z. case: x => x0 x1. case: y => y0 y1. case: z => z0 z1. simpl. move => [A B] [C D].
split ; by [apply Ole_trans with y0 | apply Ole_trans with y1].
Qed.

Canonical Structure prod_ordMixin := OrdMixin prod_ord_axiom.
Canonical Structure prod_ordType := Eval hnf in OrdType prod_ordMixin.

Lemma fst_mon : monotonic (@fst O1 O2).
case => x1 x2. case => y1 y2. by case => X Y.
Qed.

Definition Fst := Eval hnf in mk_fmono fst_mon.

Lemma snd_mon : monotonic (@snd O1 O2).
case => x1 x2. case => y1 y2. by case => X Y.
Qed.

Definition Snd := Eval hnf in mk_fmono snd_mon.

Lemma Prod_fun_mono Z (f:Z =-> O1) (g:Z =-> O2) : monotonic (fun p => (f p, g p)).
move => Z f g x y l. by split ; apply fmonotonic.
Qed.

Definition Prod_fun Z (f:Z =-> O1) (g:Z =-> O2) := Eval hnf in mk_fmono (Prod_fun_mono f g).

End ordCatProd.

Lemma fmon_eq_intro : forall (O1 O2:ordType) (f g:O1 =-> O2), (forall n, f n =-= g n) -> f =-= g.
move => O0 O1 f g X. split => x. by apply (proj1 (X x)).  by apply (proj2 (X x)). 
Qed.
Hint Resolve fmon_eq_intro.

Lemma fmon_eq_elim : forall (O1 O2:ordType) (f g:O1 =-> O2), f =-= g ->forall n, f n =-= g n.
move => O1 O2 f g e n. split ; by [apply (proj1 e) | apply (proj2 e)].
Qed.
Hint Immediate fmon_eq_elim.

Lemma ordProdCatAxiom : @CatProduct.axiom _ prod_ordType (@Fst) (@Snd) Prod_fun.
move => O0 O1 O2 f g. split. split ; by apply: fmon_eq_intro.
move => h [X Y]. apply: fmon_eq_intro => x. have X':=fmon_eq_elim X x. have Y':=fmon_eq_elim Y x.
simpl in X', Y'. by split ; destruct X'; destruct Y'.
Qed.

Canonical Structure ordProdCatMixin := prodCatMixin ordProdCatAxiom.
Canonical Structure ordProdCatType := Eval hnf in prodCatType ordProdCatMixin.

Add Parametric Morphism (O0 O1:ordType) : (@pair O0 O1)
 with signature (@Ole O0) ++> (@Ole O1) ++> (@Ole (O0 * O1))
 as pair_le_compat.
move => x y e x' y' e'. by split.
Qed.

Add Parametric Morphism (O0 O1:ordType) : (@pair O0 O1)
 with signature (@tset_eq O0 : O0 -> O0 -> Prop) ==> (@tset_eq O1 : O1 -> O1 -> Prop) ==> (@tset_eq (O0 * O1))
 as pair_eq_compat.
move => x y e x' y' e'. split. by rewrite -> e ; rewrite -> e'.
by rewrite <- e ; rewrite <- e'.
Qed.

Lemma pair1_mon (O0 O1 : ordType) (x:O0) : monotonic (fun (y:O1) => (x,y)).
move => O0 O1 x y y' l. by rewrite -> l.
Qed.

Definition Pair (O0 O1 : ordType) (x:O0) : O1 =-> (O0 * O1) := Eval hnf in mk_fmono (pair1_mon x).

Lemma Curry_mono (O0 O1 O2 : ordType) (f:O0 * O1 =-> O2) : monotonic (fun x => f << Pair _ x).
move => O1 O2 O3 f x x' L y. simpl. by apply fmonotonic.
Qed.

Definition Curry (O0 O1 O2 : ordType) (f:O0 * O1 =-> O2) : O0 =-> fmono_ordType O1 O2 := 
            Eval hnf in mk_fmono (Curry_mono f).

Lemma Ev_mon O0 O1 : monotonic (fun (p:fmono_ordType O0 O1 * O0) => fst p (snd p)).
move => O0 O1. case => f x. case => f' x'. simpl. case ; simpl => L L'.
rewrite -> L. by rewrite -> L'.
Qed.

Definition Ev O0 O1 : (fmono_ordType O0 O1) * O0 =-> O1 := Eval hnf in mk_fmono (@Ev_mon O0 O1).

Lemma ordExpAxiom : @CatExp.axiom _ fmono_ordType (@Ev) (@Curry).
move => O0 O1 O2 h. split ; first by apply: fmon_eq_intro ; case.
move => h' X. apply: fmon_eq_intro => x. apply: fmon_eq_intro => y.
simpl. by apply (fmon_eq_elim X (x,y)).
Qed.

Canonical Structure ordExpMixin := expCatMixin ordExpAxiom.
Canonical Structure ordExpType := Eval hnf in expCatType ordExpMixin.


(*=natO *)
Lemma natO_axiom : PreOrd.axiom (fun n m : nat => leq n m).
(*CLEAR*)
Proof.
move => x ; split ; clear ; first by [].
move => y z ; by apply leq_trans.
Qed.
(*CLEARED*)Canonical Structure natO_ordMixin := OrdMixin natO_axiom.
Canonical Structure natO_ordType := Eval hnf in OrdType (natO_ordMixin).
Notation natO := natO_ordType.
(*=End *)

Lemma natO_le (x y : natO) : (x <= y) = (x <= y)%N.
by [].
Qed.

(*=CPO *)
Module CPO.
Definition axiom (T:ordType) (lub : (natO =-> T) -> T) := 
        forall  (c:natO =-> T) x n, (c n <= lub c) /\ ((forall n, c n <= x) -> lub c <= x).
Record mixin_of (T:ordType) : Type := Mixin {lub: (natO =-> T) -> T; _ : axiom lub }.
Record class_of (T:Type) : Type :=
  Class {base :> PreOrd.class_of T; ext :> mixin_of (PreOrd.Pack base T) }. (*CLEAR*)

Structure type : Type := Pack { sort :> Type; _ : class_of sort ; _ : Type}.

Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack := let k T c m := Pack (@Class T c m) T in PreOrd.unpack k.
(*CLEARED*)
Coercion ordType cT := PreOrd.Pack (class cT) cT.
Definition setoidType cT := Setoid.Pack (class cT) cT.
End CPO.
Notation cpoType := CPO.type.
Notation CpoMixin := CPO.Mixin.
Notation CpoType := CPO.pack.
Canonical Structure CPO.ordType.
Canonical Structure CPO.setoidType.
(*=End *)

Bind Scope D_scope with CPO.sort.
Delimit Scope D_scope with CPO.

Open Scope D_scope.

Definition lub (T:cpoType) : (natO =-> T) -> T := Eval hnf in CPO.lub (CPO.class T).

Lemma le_lub (T:cpoType) (c : natO =-> T) (n : nat) : c n <= lub c.
case. simpl. move => T. case. simpl. move => B. case. simpl. move => l A T' c n.
by apply (proj1 (A c (c 0) n)).
Qed.

Lemma lub_le (T:cpoType) (c : natO =-> T) (x : T) : (forall n, c n <= x) -> lub c <= x.
case. simpl. move => T. case. move => B. case. simpl. move => l A T' c x C.
by apply (proj2 (A c x O)).
Qed.

Hint Resolve le_lub lub_le.

Add Parametric Relation (O:cpoType) : O (@tset_eq O : O -> O -> Prop)
       reflexivity proved by (@Oeq_refl O) symmetry proved by (@Oeq_sym O)
       transitivity proved by (@Oeq_trans O) as Oeq_CpoRelation.

Add Parametric Relation (O:cpoType) : O (@Ole O)
       reflexivity proved by (@Ole_refl O) 
       transitivity proved by (@Ole_trans O) as Ole_CpoRelation.

Add Parametric Morphism (c:cpoType) : (@lub c) 
with signature (@Ole (fmono_ordType natO c) : (natO =-> c) -> (natO =-> c) -> Prop) ++> (@Ole c) 
as lub_le_compat.
intros f g H; apply lub_le; intros.
apply Ole_trans with (g n); auto.
Qed.
Hint Resolve lub_le_compat.

Add Parametric Morphism (c:cpoType) : (@lub c) 
with signature (@tset_eq (natO =-> c) : (natO =-> c) -> (natO =-> c) -> Prop) ++> (@tset_eq c)
as lub_eq_compat.
move => f g H. split. simpl. rewrite -> (proj1 H). by apply: Ole_refl.
rewrite -> (proj2 H). by apply Ole_refl.
Qed.
Hint Resolve lub_eq_compat.

Lemma lub_mon (D:cpoType) : monotonic (@lub D).
move => D f g l. by rewrite -> l.
Qed.

Definition Lub (D:cpoType) : (natO -=> D) =-> D := mk_fmono (@lub_mon D).

(*=Cont *)
Definition continuous (D1 D2 : cpoType) (f : ordCatType D1 D2) :=
                forall c : natO =-> D1,  f (lub c) <= lub (f << c).
Module FCont. Section fcont.
 Variable O1 O2 : cpoType.
 Record mixin_of (f:fmono O1 O2) := Mixin {cont :> continuous f }.
 Record class_of (f : O1 -> O2) := 
            Class {base :> FMon.mixin_of f; ext :> mixin_of (FMon.Pack base f) }. (*CLEAR*)

Structure type : Type := Pack {sort :> O1 -> O2; _ : class_of sort; _ : O1 -> O2}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.
Definition pack := let k T c m := Pack (@Class T c m) T in FMon.unpack k.
(*CLEARED*) Coercion fmono f : fmono O1 O2 := FMon.Pack (class f) f.
End fcont. End FCont. 
Notation fcont := FCont.type. (*CLEAR*)
Notation fcontMixin := FCont.Mixin.
Notation fcontType := FCont.pack.
(*CLEARED*)
Canonical Structure FCont.fmono.
(*=End *)

Lemma fcontinuous O1 O2 (f:fcont O1 O2) : continuous f.
move => O1 O2. case. simpl. move => f. case => fm. by case.
Qed.

Hint Resolve fcontinuous.
Hint Unfold continuous.

Canonical Structure mk_fcontM (D0 D1:cpoType) (f:fmono D0 D1) (c:continuous (FMon.Pack (FMon.class f) f)) := fcontMixin c.
Definition mk_fcont (D0 D1:cpoType) (f:fmono D0 D1) (c:continuous (FMon.Pack (FMon.class f) f)) := Eval hnf in @fcontType D0 D1 f (mk_fcontM c).

Lemma oid_cont (D:cpoType) : continuous (oid D).
move => D c. by rewrite -> comp_idL.
Qed.

Definition cid (D:cpoType) := Eval hnf in mk_fcont (@oid_cont D).

Lemma ocomp_cont (D0 D1 D2 : cpoType) (f:fcont D1 D2) (g:fcont D0 D1) : continuous (ocomp f g).
move => D0 D1 D2 f g c. simpl. apply Ole_trans with (f (lub ((g:fmono D0 D1) << c))).
by apply: fmonotonic ; apply: fcontinuous.
rewrite -> (fcontinuous f ((g:fmono D0 D1) << c)). by rewrite comp_assoc.
Qed.

Definition ccomp (D0 D1 D2 : cpoType) (f:fcont D1 D2) (g:fcont D0 D1) := Eval hnf in mk_fcont (ocomp_cont f g).

Lemma fcont_ord_axiom (D1 D2 :cpoType) : PreOrd.axiom (fun (f g:fcont D1 D2) => (f:fmono D1 D2) <= g).
move => D1 D2 f. split ; first by [].
move => g h ; by apply Ole_trans.
Qed.

Canonical Structure fcont_ordMixin (D1 D2 :cpoType) := OrdMixin (@fcont_ord_axiom D1 D2).
Canonical Structure fcont_ordType (D1 D2 :cpoType) := Eval hnf in OrdType (fcont_ordMixin D1 D2).

Lemma cpoMorphSetoidAxiom (D0 D1 : cpoType) : @Setoid.axiom (fcont D0 D1) (@tset_eq (fcont_ordType D0 D1)).
move => D0 D1. split ; first by [].
split ; first by apply: Oeq_trans.
by apply: Oeq_sym.
Qed.

Canonical Structure cpoMorphSetoidMixin O0 O1 := SetoidMixin (cpoMorphSetoidAxiom O0 O1).
Canonical Structure cpoMorphSetoidType O0 O1 := Eval hnf in SetoidType (cpoMorphSetoidMixin O0 O1).

(* fcont <= *)
Definition fcont_less (A B: cpoType): relation (fcont A B) := (@Ole _).

Definition fcont_less_preorder (A B: cpoType): PreOrder (@fcont_less A B).
move => A B. split ;first by move => x.
move => x y z. by apply Ole_trans.
Defined.

Existing Instance fcont_less_preorder.

Add Parametric Morphism (A B : cpoType) :
  (@FCont.sort A B) with signature (@fcont_less A B ++> @Ole A ++> @Ole B)
 as fcont_le_compat.
move => x y l x' y' l'. apply Ole_trans with (y:=x y') ; first by apply: fmonotonic.
by apply l.
Qed.

(* fcont == *)

Definition fcont_equal (A B: cpoType): relation (fcont A B) := (@tset_eq _).

Definition fcont_equal_equivalence (A B: cpoType): Equivalence (@fcont_equal A B).
intros A B. split.
- move => x. by apply: Oeq_refl.
- move => x y. by apply: Oeq_sym.
- move => x y z. by apply: Oeq_trans.
Defined.

Existing Instance fcont_equal_equivalence.

Add Parametric Morphism (A B : cpoType) :
  (@FCont.sort A B) with signature (@fcont_equal A B ==> @tset_eq A ==> @tset_eq B)
 as fcont_eq_compat.
move => x y l x' y' l'. apply Oeq_trans with (y:=x y') ; first by apply: fmon_stable.
by apply (fmon_eq_elim l y').
Qed.

(*=cpoCat *)
Lemma cpoCatAxiom : Category.axiom ccomp cid.
(*CLEAR*)
split ; first by move => D0 D1 f ; apply: fmon_eq_intro.
split ; first by move => D0 D1 f ; apply: fmon_eq_intro.
split ; first by move => D0 D1 D2 D3 f g h ; apply: fmon_eq_intro.
move => D0 D1 D2 f f' g g' e e'. apply: fmon_eq_intro => x. simpl. rewrite -> e. by rewrite -> e'.
Qed.

SearchAbout "CatType".
(*CLEARED*)Canonical Structure cpoCatMixin := CatMixin cpoCatAxiom.
Canonical Structure cpoCatType := Eval hnf in CatType cpoCatMixin.
(*=End *)

Definition prod_lub (D1 D2:cpoType) (f : natO =-> prod_ordType D1 D2) := (lub (pi1 << f), lub (pi2 << f)).

Lemma prod_cpo_axiom D1 D2 : CPO.axiom (prod_lub (D1:=D1) (D2:=D2)).
move => D1 D2 c x n ; split ; clear.
apply Ole_trans with (fst (c n), snd (c n)) ; first by case (c n).
by split ; simpl ; rewrite <- (le_lub _ n).
move => C. by split ; simpl ; apply lub_le => m ; [apply: (fmonotonic (@Fst D1 D2)) | apply: (fmonotonic (@Snd D1 D2))].
Qed.

Canonical Structure prod_cpoMixin D1 D2 := CpoMixin (@prod_cpo_axiom D1 D2).
Canonical Structure prod_cpoType D1 D2 := Eval hnf in CpoType (prod_cpoMixin D1 D2).

Lemma Prod_fun_cont (D1 D2 D3:cpoType) (f:D1=->D2) (g:D1=->D3) : continuous (<|f : ordCatType _ _, g|>).
intros D1 D2 D3 f g c.
simpl. split ; simpl ; rewrite comp_assoc.
- rewrite (fcontinuous f). by rewrite -> prod_fun_fst.
- rewrite fcontinuous. by rewrite prod_fun_snd.
Qed.

Definition PROD_fun (D2 D3 D1:cpoCatType)(f:D1=->D2)(g:D1=->D3) : D1 =-> prod_cpoType D2 D3 :=
  Eval hnf in mk_fcont (Prod_fun_cont f g).

Lemma Fst_cont (D1 D2 : cpoType) : continuous (@Fst D1 D2).
by move => D1 D2 c.
Qed.

Definition FST (D1 D2 : cpoType) : prod_cpoType D1 D2 =-> D1 := mk_fcont (@Fst_cont D1 D2).

Lemma Snd_cont (D1 D2 : cpoType) : continuous (@Snd D1 D2).
by move => D1 D2 c.
Qed.

Definition SND (D1 D2 : cpoType) : prod_cpoType D1 D2 =-> D2 := mk_fcont (@Snd_cont D1 D2).

Lemma cpoProdCatAxiom : @CatProduct.axiom _ prod_cpoType FST SND PROD_fun.
move => X Y Z f g.
split ; first by split ; [apply: (@prod_fun_fst ordProdCatType) | apply: (@prod_fun_snd ordProdCatType)].
move => h [A B].
by apply: (@prod_fun_unique ordProdCatType).
Qed.

Canonical Structure cpoProdCatMixin := prodCatMixin cpoProdCatAxiom.
Canonical Structure cpoProdCatType := Eval hnf in prodCatType cpoProdCatMixin.

Add Parametric Morphism (O0 O1:cpoType) : (@pair O0 O1)
 with signature (@Ole O0 : O0 -> O0 -> Prop) ++> (@Ole O1 : O1 -> O1 -> Prop) ++> (@Ole (O0 * O1))
 as pair_cpo_le_compat.
move => x y e x' y' e'. by split.
Qed.

Add Parametric Morphism (O0 O1:cpoType) : (@pair O0 O1)
 with signature (@tset_eq O0 : O0 -> O0 -> Prop) ==> (@tset_eq O1 : O1 -> O1 -> Prop) ==> (@tset_eq (O0 * O1))
 as pair_cpo_eq_compat.
move => x y e x' y' e'. case: e => e0 e1 ; case: e' => e2 e3. by split.
Qed.

Lemma const_mon (O1 O2 : ordType) (y:O2) : monotonic (fun _ : O1 => y).
by move => O1 O2 y x x'.
Qed.

Definition fmon_cte (O1 O2 : ordType) (y:O2) : O1 =-> O2 := Eval hnf in mk_fmono (@const_mon O1 O2 y).

Lemma lub_const (D:cpoType) (x:D) : lub (fmon_cte natO x) =-= x.
move => D x. split. by apply: lub_le. by apply (le_lub (fmon_cte natO x) O).
Qed.

Definition Fcontit_mono (D1 D2:cpoType) : monotonic (fun f:fcont_ordType D1 D2 => (f:(D1:ordType) -=> D2)) :=
 fun x y => id.

Definition Fcontit (D1 D2:cpoType) := Eval hnf in mk_fmono (@Fcontit_mono D1 D2).

Lemma eq_mono (D0 D1:ordType) (f:D0 -> D1) (g:D0 =-> D1) : (forall x, f x =-= g x) -> monotonic f.
move=> D0 D1 f g X x x' L. do 2 rewrite -> X. by rewrite L.
Qed.

Definition gen_mono (D0 D1:ordType) (f:D0 -> D1) (g:D0 =-> D1) (X:forall x, f x =-= g x) : D0 =-> D1 :=
   Eval hnf in mk_fmono (eq_mono X).

Lemma fcont_app_def_eq (O:ordType) (D1 D2:cpoType) (f: O =-> (fcont_ordType D1 D2)) (x:D1) :
  forall y, (fun y => f y x) y =-= (exp_fun(uncurry (Fcontit _ _ << f) << <|pi2,pi1|>) x) y.
by [].
Qed.

Lemma fmon_app_def_eq (O D1 D2:ordType) (f: O =-> D1 -=> D2) (x:D1) :
  forall y, (fun y => f y x) y =-= (exp_fun(uncurry (f:ordCatType _ _) << <|pi2,pi1|>) x) y.
by [].
Qed.

Definition fmon_app (O D1 D2:ordType) (f: O =-> D1 -=> D2) (x:D1) : O =-> D2 :=
  Eval hnf in gen_mono (fmon_app_def_eq f x).

Lemma fmon_app_eq (O D1 D2:ordType) (f: O =-> D1 -=> D2) (x:D1) :
  fmon_app f x =-= (exp_fun((uncurry f:ordCatType _ _) << <|pi2,pi1|>) x).
move => O D1 D2 f x. by apply fmon_eq_intro => y.
Qed.

Definition fcont_app (O:ordType) (D1 D2:cpoType) (f: O =-> (fcont_ordType D1 D2)) (x:D1) : O =-> D2 :=
  Eval hnf in gen_mono (fcont_app_def_eq f x).

Lemma fcont_app_eq (O:ordType) (D1 D2:cpoType) (f: O =-> (fcont_ordType D1 D2)) (x:D1) : 
  fcont_app f x =-= (exp_fun((uncurry (Fcontit _ _ << f):ordCatType _ _) << <|pi2,pi1|>) x).
move => O D1 D2 f x. by apply fmon_eq_intro => y.
Qed.

Lemma fcont_lub_mono (D1 D2:cpoType) (c:natO =-> (fcont_ordType D1 D2)) : monotonic (fcont_app c).
move => D1 D2 c x y l n. simpl. by rewrite -> l.
Qed.

Lemma fcont_lub_cont (D1 D2:cpoType) (c:natO =-> (fcont_ordType D1 D2)) : continuous (Lub _ << mk_fmono (fcont_lub_mono c)).
move => D1 D2 c c'. simpl. apply lub_le => i. simpl.
rewrite (fcontinuous (c i)). apply lub_le_compat => j. simpl. by apply: (Ole_trans _ (le_lub _ i)).
Qed.

Definition fcont_lub (D1 D2:cpoType) (c:natO =-> (fcont_ordType D1 D2)) : D1 =-> D2 :=
  Eval hnf in mk_fcont (fcont_lub_cont c).

Lemma fcont_lub_simpl (D1 D2:cpoType) (c:natO =-> (fcont_ordType D1 D2)) (x:D1) : 
  fcont_lub c x = lub (fcont_app c x).
by [].
Qed.

Lemma fcont_cpo_axiom (D0 D1:cpoType) : CPO.axiom (@fcont_lub D0 D1).
move => D0 D1 c x n. split.
- move => a. simpl. by rewrite <- (le_lub _ n).
- move => C. move => y. simpl. apply: lub_le => m. specialize (C m). simpl. by rewrite -> C.
Qed.

Canonical Structure fcont_cpoMixin (D0 D1:cpoType) := CpoMixin (@fcont_cpo_axiom D0 D1).
Canonical Structure fcont_cpoType (D0 D1:cpoType) := Eval hnf in CpoType (fcont_cpoMixin D0 D1).

Lemma fcont_app2_cont (D0 D1 D2:cpoType) (f: D0 =-> (fcont_cpoType D1 D2)) (x:D1) : continuous (fcont_app f x).
move => D0 D1 D2 f x c. simpl. rewrite (fcontinuous f). simpl. by apply lub_le_compat => n.
Qed.

Definition Fcont_app (D0 D1 D2:cpoType) (f: D0 =-> (fcont_cpoType D1 D2)) (x:D1) : D0 =-> D2 :=
   Eval hnf in mk_fcont (fcont_app2_cont f x).

Lemma Pair_cont (D0 D1 : cpoType) (x:D0) : continuous (Pair D1 x).
move => D0 D1 x c. simpl. split.
- simpl. by apply: (Ole_trans _ (le_lub (pi1 << (Pair D1 x << c)) O)).
- simpl. by apply lub_le_compat => i.
Qed.

Definition PAIR (D0 D1 : cpoType) (x:D0) : D1 =-> D0 * D1 := Eval hnf in mk_fcont (Pair_cont x).

Lemma Curry2_mon (D0 D1 D2 : cpoType) (f:D0 * D1 =-> D2) : monotonic (fun x => f << PAIR _ x).
move => D0 D1 D2 f x x' l y. simpl. by rewrite -> l.
Qed.

Definition CURRY_mon (D0 D1 D2 : cpoType) (f:D0 * D1 =-> D2) := Eval hnf in mk_fmono (Curry2_mon f).

Lemma Curry2_cont (D0 D1 D2 : cpoType) (f:D0 * D1 =-> D2) : continuous (CURRY_mon f).
move => D1 D2 D3 f c x. simpl. rewrite {1} (Oeq_sym (lub_const x)).
rewrite - {1} (prod_fun_snd c (fmon_cte natO x)).
rewrite - {1} (prod_fun_fst c (fmon_cte natO x)).
apply: (Ole_trans (fcontinuous f _)).
by apply lub_le_compat => i.
Qed.

Definition CURRY (D0 D1 D2 : cpoType) (f:D0 * D1 =-> D2) := Eval hnf in mk_fcont (Curry2_cont f).

Lemma Ev1_mon (D0 D1 : cpoType) : monotonic (fun x : ((fcont_cpoType D0 D1) * D0) => (fst x) (snd x)).
move => D0 D1. simpl. case => f x. case => f' x'. case ; simpl => L L'.
rewrite -> L. by rewrite -> L'.
Qed.

Definition EV1 (D0 D1 : cpoType) := Eval hnf in mk_fmono (@Ev1_mon D0 D1).

Lemma Ev_cont (D0 D1 : cpoType) : continuous (@EV1 D0 D1).
move => D0 D1 c. simpl.
apply Ole_trans with ((lub (pi1 << c)) (lub (pi2 << c))) ; first by apply: lub_le_compat => n.
rewrite -> (fcontinuous (lub (pi1 << c)) (pi2 << c)).
apply lub_le => i. simpl. apply lub_le => j. simpl. apply: (Ole_trans _ (le_lub _ (j+i))).
simpl. apply Ole_trans with (Fst _ _ (c j) (Snd _ _ (c i))) ; first by [].
rewrite -> (fmonotonic c (leq_addl j i)). by rewrite -> (fmonotonic c (leq_addr i j)).
Qed.

Definition EV (D0 D1 : cpoType) : (fcont_cpoType D0 D1 * D0) =-> D1 := Eval hnf in mk_fcont (@Ev_cont D0 D1).

Lemma cpoExpAxiom : @CatExp.axiom _ fcont_cpoType (@EV) (@CURRY).
move => D0 D1 D2 h. split ; first by apply: fmon_eq_intro ; case.
move => h' X. apply: fmon_eq_intro => x. apply: fmon_eq_intro => y.
simpl. by apply (fmon_eq_elim X (x,y)).
Qed.

Canonical Structure cpoExpMixin := expCatMixin cpoExpAxiom.
Canonical Structure cpoExpType := Eval hnf in expCatType cpoExpMixin.

Module CPPO.

Record class_of (T:Type) : Type := Class 
  { base1 :> CPO.class_of T;
    ext :> Pointed.mixin_of (PreOrd.Pack base1 T)}.

Coercion base2 (T:Type) (c:class_of T) := Pointed.Class c.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack := let k T c m := Pack (@Class T c m) T in CPO.unpack k.

Coercion cpoType (cT:type) := CPO.Pack (class cT) cT.
Definition ordType (cT:type) := PreOrd.Pack (class cT) cT.
Definition pointedType (cT:type) := Pointed.Pack (class cT) cT.
Definition setoidType (cT:type) := Setoid.Pack (class cT) cT.

End CPPO.

Notation cppoType := CPPO.type.
Notation CppoType := CPPO.pack.

Canonical Structure CPPO.cpoType.
Canonical Structure CPPO.ordType.
Canonical Structure CPPO.pointedType.
Canonical Structure CPPO.setoidType.

Definition strict (D E:cppoType) (f:D -> E) := f PBot =-= PBot.

Lemma cppoCatAxiom : @Category.axiom cppoType cpoMorphSetoidType (fun D0 D1 D2 => @ccomp D0 D1 D2) (fun D0 => @cid D0).
split ; first by move => D0 D1 D2 ; apply: (proj1 (cpoCatAxiom)).
split ; first by move => D0 D1 D2 ; apply: (proj1 (proj2 (cpoCatAxiom))).
split ; first by move => D0 D1 D2 D3 ; apply: (proj1 (proj2 (proj2 (cpoCatAxiom)))).
move => D0 D1 D2 ; apply: (proj2 (proj2 (proj2 (cpoCatAxiom)))).
Qed.

Canonical Structure cppoCatMixin := CatMixin cppoCatAxiom.
Canonical Structure cppoCatType := Eval hnf in CatType cppoCatMixin.

Lemma cppoProdPointedAxiom (D0 D1:cppoType) : Pointed.axiom (PBot:D0,PBot : D1).
move => D0 D1. split ; simpl ; apply: leastP.
Qed.

Canonical Structure prod_cppoMixin (D0 D1:cppoType) := PointedMixin (@cppoProdPointedAxiom D0 D1).
Canonical Structure prod_cppoType (D0 D1:cppoType) := Eval hnf in CppoType (prod_cppoMixin D0 D1).

Lemma cppoProdCatAxiom : @CatProduct.axiom _ prod_cppoType (fun A B => @FST A B) (fun A B => @SND A B) (fun A B C => @PROD_fun A B C).
move => X Y Z f g.
split ; first by apply (proj1 (@cpoProdCatAxiom X Y Z f g)).
move => m. by apply (proj2 (@cpoProdCatAxiom X Y Z f g) m).
Qed.

Canonical Structure cppoProdCatMixin := prodCatMixin cppoProdCatAxiom.
Canonical Structure cppoProdCatType := Eval hnf in prodCatType cppoProdCatMixin.

Lemma const_cont (D E : cpoType) (x:E) : continuous (fmon_cte D x).
move => D E x c. simpl. by apply: (Ole_trans _ (le_lub _ O)).
Qed.

Definition const (D E:cpoType) x : D =-> E := Eval hnf in mk_fcont (const_cont x).

Lemma const_com D E F x h : @const D E x =-= @const F E x << h.
move => D E F x h. by apply: fmon_eq_intro.
Qed.

Lemma fcont_cppo_axiom D0 (D1 : cppoType) : Pointed.axiom (const D0 (PBot:D1)).
move => D0 D1 f x. simpl. apply: leastP.
Qed.

Canonical Structure exp_cppoMixin D0 (D1:cppoType) := PointedMixin (@fcont_cppo_axiom D0 D1).
Canonical Structure exp_cppoType D0 (D1:cppoType) := Eval hnf in CppoType (exp_cppoMixin D0 D1).

Lemma cppoExpAxiom : @CatExp.axiom cppoProdCatType exp_cppoType (fun D0 D1 => @EV D0 D1) (fun D0 D1 D2 => @CURRY D0 D1 D2).
move => D0 D1 D2 h.
split. by apply (proj1 (@cpoExpAxiom D0 D1 D2 h)).
move => h'. by apply (proj2 (@cpoExpAxiom D0 D1 D2 h) h').
Qed.

Canonical Structure cppoExpMixin := expCatMixin cppoExpAxiom.
Canonical Structure cppoExpType := Eval hnf in expCatType cppoExpMixin.

Lemma discrete_cpoAxiom T : @CPO.axiom (discrete_ordType T) (fun c => c 0).
move => T c e n. split.
- have L:c 0 <= c n by apply fmonotonic.
  have E:c 0 = c n by apply L. by rewrite E.
- move => X. by specialize (X 0).
Qed.

Canonical Structure discrete_cpoMixin T := CpoMixin (@discrete_cpoAxiom T).
Definition discrete_cpoType T := Eval hnf in CpoType (@discrete_cpoMixin (discrete_ordType T)).

Canonical Structure nat_cpoType := Eval hnf in discrete_cpoType nat.
Canonical Structure bool_cpoType := Eval hnf in discrete_cpoType bool.

Definition monic (D E:ordType) (f:D =-> E) := forall x y, f x <= f y -> x <= y.

Lemma subordAxiom (D:ordType) (P:D -> Prop) : PreOrd.axiom 
   (fun (x' y:{x : D | P x}) => match x' with exist x _ => match y with exist y _ => @Ole D x y end end).
move => D P. case => a Pa. split ; first by []. case => b Pb. case => c Pc.
by apply Ole_trans.
Qed.

Canonical Structure sub_ordMixin D P := OrdMixin (@subordAxiom (D:ordType) (P:D -> Prop)).
Canonical Structure sub_ordType D P := Eval hnf in OrdType (@sub_ordMixin D P).

Definition SubOrde (D:ordType) (P:D -> Prop) (d:D)  (X:P d) : sub_ordType P := exist (fun x => P x) d X.

Implicit Arguments SubOrde [D P].

Lemma InheritFun_mono D (E:ordType) (Q:E->Prop) (f:D =-> E) (p:forall d, Q (f d)) : monotonic (fun d => @SubOrde E Q (f d) (p d)).
move => D E Q f p x y lxy. by apply: fmonotonic.
Qed.

Definition InheritFunm D (E:ordType) (Q:E->Prop) (f:D =-> E) (p:forall d, Q (f d)) :
 D =-> sub_ordType Q := Eval hnf in mk_fmono (InheritFun_mono p).

Implicit Arguments InheritFunm [D E Q].

Lemma Forget_mono D P : monotonic (fun (O:@sub_ordType D P) => match O with exist x _ => x end).
move => D P. case => x px. by case.
Qed.

Definition Forgetm D P : (@sub_ordType D P) =-> D := Eval hnf in mk_fmono (@Forget_mono D P).

Lemma fmonD_mon D (E:ordType) (f:D -> E) : @monotonic (discrete_cpoType D) E f.
move => D E f x y l. by rewrite -> l.
Qed.

Definition fmonD D (E:ordType) (f:D -> E) : discrete_ordType D =-> E := Eval hnf in mk_fmono (fmonD_mon f).

Lemma ford_axiom (A:Type) (O:ordType) : PreOrd.axiom (fun f g:A->O => forall x, f x <= g x).
move => A O f.
split ; first by apply (proj1 (@fmono_axiom (discrete_ordType A) O (fmonD f))).
move => y z X Y. by apply (proj2 (@fmono_axiom (discrete_ordType A) O (fmonD f)) (fmonD y) (fmonD z) X Y).
Qed.

Canonical Structure ford_ordMixin (T:Type) (O:ordType) := OrdMixin (@ford_axiom T O).
Definition ford_ordType T O := Eval hnf in OrdType (ford_ordMixin T O).

Lemma lub_comp_le :
    forall (D1 D2 : cpoType) (f:ordCatType D1 D2) (h : natO =-> D1),  lub (f << h) <= f (lub h).
intros; apply lub_le; simpl; intros.
apply (fmonotonic f); auto.
Qed.
Hint Resolve lub_comp_le.

Lemma lub_comp_eq :
    forall (D1 D2 : cpoType) (f:cpoCatType D1 D2) (h : natO =-> D1), f (lub h) =-= lub ((f:ordCatType _ _) << h).
move => D1 D2 f g. apply: Ole_antisym ; last by apply: lub_comp_le.
rewrite fcontinuous. apply lub_le => n. simpl. by apply: (Ole_trans _ (le_lub _ n)).
Qed.
Hint Resolve lub_comp_eq.

Lemma mseq_lift_left_mon (O:ordType) (f:natO =-> O) (n:nat) : monotonic (fun i => f (n+i)%N).
move => O f n x y l. apply fmonotonic. unfold Ole. simpl. rewrite -> (leq_add2l n x y). by apply l.
Qed.

Definition mseq_lift_left (O:ordType) (f:natO =-> O) (n:nat) := Eval hnf in mk_fmono (mseq_lift_left_mon f n).

Lemma lub_lift_left : forall (D:cpoType) (f:natO =-> D) n, lub f =-= lub (mseq_lift_left f n).
move => D f n. apply: Ole_antisym.
- apply lub_le. move => m. rewrite <- (le_lub _ m). simpl. apply fmonotonic. rewrite natO_le. by rewrite leq_addl.
- apply lub_le. move => m. by rewrite <- (le_lub _ (n+m)).
Qed.
Hint Resolve lub_lift_left.

Lemma lub_fun_mon (O:ordType) (D:cpoType) (h : natO =-> O -=> D) : monotonic (fun m => lub (fmon_app h m)).
move => O D h x y l. apply lub_le_compat => n. simpl. by rewrite -> l.
Qed.

Definition lub_fun (O:ordType) (D:cpoType) (h : natO =-> O -=> D) : O =-> D :=
  Eval hnf in mk_fmono (lub_fun_mon h).

Lemma fmon_cpo_axiom (O:ordType) (D:cpoType) : @CPO.axiom (O -=> D) (lub_fun (O:=O) (D:=D)).
move => O D c x n ; split => e ; simpl ; first by rewrite <- (le_lub _ n).
move => a. simpl. apply lub_le. move => m. simpl. by rewrite (e m).
Qed.

Canonical Structure fmon_cpoMixin (O:ordType) (D:cpoType) := CpoMixin (@fmon_cpo_axiom O D).
Canonical Structure fmon_cpoType (O:ordType) (D:cpoType) := Eval hnf in CpoType (@fmon_cpoMixin O D).

Definition fmon_shift (O1 O2 O3:ordType) (f: O1 =-> O2 -=> O3) : O2 =-> O1 -=> O3 :=
  exp_fun (uncurry f << <|pi2,pi1|>).

Lemma fmon_fcont_shift_cont (O:ordType) (D1 D2:cpoType) (f: O =-> D1 -=> D2) : continuous (fmon_shift (Fcontit D1 D2<<f)).
move => O D1 D2 f c x. simpl. rewrite (fcontinuous (f x)). by apply lub_le_compat => i.
Qed.

Definition fmon_fcont_shift (O:ordType) (D1 D2:cpoType) (f: O =-> D1 -=> D2) : D1 =-> fmon_cpoType O D2 :=
  Eval hnf in mk_fcont (fmon_fcont_shift_cont f).

Lemma fcont_app_continuous : 
       forall (O:ordType) (D1 D2:cpoType) (f: O =-> D1 -=> D2) (h:natO =-> D1),
            fcont_app f (lub h) <= lub ((fmon_fcont_shift f:ordCatType _ _) << h).
move => O D1 D2 f h x. simpl. rewrite (fcontinuous (f x)). by apply lub_le_compat.
Qed.

Lemma fmon_diag_mon (O1 O2:ordType)(h:O1 =-> (O1 -=> O2)) : monotonic (fun n => h n n).
move => O1 O2 h x y l. by rewrite -> l.
Qed.

Definition fmon_diag (O1 O2:ordType)(h:O1 =-> (O1 -=> O2)) : O1 =-> O2 :=
  Eval hnf in mk_fmono (fmon_diag_mon h).

Lemma lub_diag D (c:ordCatType natO (fmon_cpoType natO D)) : lub (lub c) =-= lub (fmon_diag c).
move => D c. apply: Ole_antisym.
- apply: lub_le => i. apply: lub_le => j. apply: (Ole_trans _ (le_lub _ (i+j))).
  simpl. rewrite -> (fmonotonic c (leq_addl i j)).
  by rewrite -> (fmonotonic (c (i+j)%N) (leq_addr j i)).
- apply: lub_le => i. by do 2 apply: (Ole_trans _ (le_lub _ i)).
Qed.

Lemma zero_ord_axiom : PreOrd.axiom (fun x y : Empty => True).
by case.
Qed.

Canonical Structure zero_ordMixin := OrdMixin zero_ord_axiom.
Canonical Structure zero_ordType := Eval hnf in OrdType zero_ordMixin.

Lemma ordZeroAxiom : @CatInitial.axiom ordCatType zero_ordType.
move => C f g. apply: fmon_eq_intro. by case.
Qed.

Lemma Zero_fun_mono (X:ordType) : monotonic (fun (x:Empty) => match x with end:X).
move => X. by case.
Qed.

Definition Zero_fun X : zero_ordType =-> X := Eval hnf in mk_fmono (@Zero_fun_mono X).

Canonical Structure ordInitialMixin := initialCatMixin Zero_fun ordZeroAxiom.
Canonical Structure ordInitialType := Eval hnf in initialCatType ordInitialMixin.

Lemma zero_cpo_axiom : @CPO.axiom zero_ordType (fun (c:natO =-> Zero) => c 0).
move => c. by case.
Qed.

Canonical Structure zero_cpoMixin := CpoMixin zero_cpo_axiom.
Canonical Structure zero_cpoType := Eval hnf in CpoType zero_cpoMixin.

Lemma cpoZeroAxiom : @CatInitial.axiom cpoCatType zero_cpoType.
move => C f g. by apply: fmon_eq_intro.
Qed.

Lemma ZERO_fun_cont (X:cpoType) : continuous (@Zero_fun X).
move => X c. simpl. by case: (lub c).
Qed.

Definition ZERO_fun X : zero_cpoType =-> X := Eval hnf in mk_fcont (ZERO_fun_cont X).

Canonical Structure cpoInitialMixin := initialCatMixin ZERO_fun cpoZeroAxiom.
Canonical Structure cpoInitialType := Eval hnf in initialCatType cpoInitialMixin.

Lemma one_ord_axiom : PreOrd.axiom (fun x y : unit => True).
by case.
Qed.

Canonical Structure one_ordMixin := OrdMixin one_ord_axiom.
Canonical Structure one_ordType := Eval hnf in OrdType one_ordMixin.

Lemma ordOneAxiom : @CatTerminal.axiom ordCatType one_ordType.
move => C f g. apply: fmon_eq_intro => x. case: (f x). by case: (g x).
Qed.

Canonical Structure ordTerminalMixin := terminalCatMixin (fun O1 => fmon_cte O1 tt) ordOneAxiom.
Canonical Structure ordTerminalType := Eval hnf in terminalCatType ordTerminalMixin.

Lemma one_cpo_axiom : @CPO.axiom one_ordType (fun (c:natO =-> One) => tt).
move => c x n. split ; first by case: (c n).
by move => X ; case x.
Qed.

Canonical Structure one_cpoMixin := CpoMixin one_cpo_axiom.
Canonical Structure one_cpoType := Eval hnf in CpoType one_cpoMixin.

Lemma cpoOneAxiom : @CatTerminal.axiom cpoCatType one_cpoType.
move => C f g. apply: fmon_eq_intro => x. case: (f x). by case: (g x).
Qed.

Canonical Structure cpoTerminalMixin := terminalCatMixin (fun D => const D tt) cpoOneAxiom.
Canonical Structure cpoTerminalType := Eval hnf in terminalCatType cpoTerminalMixin.

Lemma one_pointedAxiom : Pointed.axiom tt.
by case.
Qed.

Canonical Structure one_pointedMixin := PointedMixin one_pointedAxiom.
Canonical Structure one_pointedType := Eval hnf in PointedType one_pointedMixin.

Canonical Structure one_cppoType := Eval hnf in CppoType one_pointedMixin.

Lemma cppoOneAxiom : CatTerminal.axiom one_cppoType.
move => C f g. by apply: (cpoOneAxiom).
Qed.

Canonical Structure cppoTerminalMixin := terminalCatMixin (fun D => const D tt : cppoCatType D one_cppoType) cppoOneAxiom.
Canonical Structure cppoTerminalType := Eval hnf in terminalCatType cppoTerminalMixin.

Lemma eq_cont (D0 D1:cpoType) (f:D0 -> D1) (g:D0 =-> D1) (X:forall x, f x =-= g x) : continuous (gen_mono X).
move => D0 D1 f g X c. simpl. rewrite -> (X (lub c)). rewrite -> (fcontinuous g c).
apply lub_le_compat => n. simpl. by rewrite -> (X (c n)).
Qed.

Definition gen_cont (D0 D1:cpoType) (f:D0 -> D1) (g:D0 =-> D1) (X:forall x, f x =-= g x) := Eval hnf in mk_fcont (eq_cont X).

Add Parametric Relation (O O':cpoType) : (O =-> O') (@Ole (fcont_ordType O O') : (O =-> O') -> (O =-> O') -> Prop)
       reflexivity proved by (@Ole_refl _) 
       transitivity proved by (@Ole_trans _) as Ole_XRelation.

Add Parametric Relation (O O':ordType) : (O =-> O') (@Ole (O -=> O') : (O =-> O') -> (O =-> O') -> Prop)
       reflexivity proved by (@Ole_refl _) 
       transitivity proved by (@Ole_trans _) as Ole_XXRelation.

Add Parametric Morphism (D1 D2 D3:cpoType) : (@Category.comp cpoCatType D1 D2 D3)
with signature (@Ole (fcont_ordType D2 D3) : (D2 =-> D3) -> (D2 =-> D3) -> Prop) ++>
               (@Ole (fcont_ordType D1 D2) : (D1 =-> D2) -> (D1 =-> D2) -> Prop) ++>
               (@Ole (fcont_ordType D1 D3) : (D1 =-> D3) -> (D1 =-> D3) -> Prop)
as comp_le_compat.
move => f g l f' g' l' x.
simpl. rewrite -> l. by rewrite -> l'.
Qed.

Add Parametric Morphism (D1 D2 D3:ordType) : (@Category.comp ordCatType D1 D2 D3)
with signature (@Ole (D2 -=> D3) : (D2 =-> D3) -> (D2 =-> D3) -> Prop) ++>
               (@Ole (D1 -=> D2) : (D1 =-> D2) -> (D1 =-> D2) -> Prop) ++>
               (@Ole (D1 -=> D3) : (D1 =-> D3) -> (D1 =-> D3) -> Prop)
as comp_le_ord_compat.
move => f g l f' g' l' x.
simpl. rewrite -> l. by rewrite -> l'.
Qed.

Lemma ccomp_mon (D1 D2 D3:cpoType) : monotonic (fun (p:(D2 -=> D3) * (D1 -=> D2)) => (fst p : cpoCatType _ _) << snd p).
move => D1 D2 D3. case => f g. case => f' g'. simpl.
case ; simpl => l l'. rewrite -> l. by rewrite -> l'.
Qed.

Definition Ccomp (D1 D2 D3:cpoType) := Eval hnf in mk_fmono (@ccomp_mon D1 D2 D3).

Lemma Ccomp_cont (D1 D2 D3:cpoType) : continuous (@Ccomp D1 D2 D3).
move => D1 D2 D3 c x. simpl.
rewrite -> fcont_app_continuous. rewrite lub_diag. by apply lub_le_compat => i.
Qed.

Definition CCOMP (D1 D2 D3:cpoType) := Eval hnf in mk_fcont (@Ccomp_cont D1 D2 D3).

Lemma comp_lub_eq (D0 D1 D2 :cpoType) (f:D1 =-> D2) (c:natO =-> fcont_ordType D0 D1) :
   f << lub c =-= lub ((@exp_fun _ (D1 -=> D2) _ _ (CCOMP D0 D1 D2) f : ordCatType _ _) << c).
move => D0 D1 D2 f c. apply: fmon_eq_intro => d. simpl. rewrite lub_comp_eq.
apply lub_eq_compat. by apply fmon_eq_intro => n.
Qed.

Lemma lub_comp (D0 D1 D2 :cpoType) (f:D0 =-> D1) (c:natO =-> fcont_ordType D1 D2) :
   (lub c : cpoCatType _ _) << f =-= lub ((@exp_fun _ (D0 -=> D1) _ _ (CCOMP D0 D1 D2 << <|pi2,pi1|>) f : ordCatType _ _) << c).
move => D0 D1 D2 f c. apply: fmon_eq_intro => d. simpl.
apply lub_eq_compat. by apply fmon_eq_intro => n.
Qed.

Lemma lub_comp_both (X Y Z:cpoType) (c:natO =-> fcont_ordType X Y) (c':natO =-> fcont_ordType Y Z) :
  (lub c' : cpoCatType _ _) << lub c =-= lub ( (CCOMP _ _ _ : ordCatType _ _) << <|c', c|>).
move => X Y Z c c'.
have a:=@lub_comp_eq _ _ ( ((CCOMP X Y Z))) (<|c',c|>). rewrite <- a.
apply: comp_eq_compat. simpl. by rewrite prod_fun_fst.
simpl. by rewrite prod_fun_snd.
Qed.

Section OrdProdI.
Variable (I:Type) (O:I -> ordType).

Lemma prodI_ord_axiom : PreOrd.axiom (fun p1 p2 :(forall i:I, O i) => forall i:I, p1 i <= p2 i).
move => x ; split ; clear ; first by [].
move => y z X Y i. rewrite (X i). by rewrite (Y i).
Qed.

Canonical Structure prodI_ordMixin := OrdMixin prodI_ord_axiom.
Canonical Structure prodI_ordType := Eval hnf in OrdType prodI_ordMixin.

Lemma Proj_monotonic (i:I) : monotonic (fun (x:prodI_ordType ) => x i).
move => i x y l. by apply l.
Qed.

Definition Proj (i:I) : prodI_ordType =-> O i := Eval hnf in mk_fmono (Proj_monotonic i).

Lemma prodi_fun_mon (D:ordType) (f:forall i:I, D =-> O i) : monotonic (fun d => (fun i => f i d):prodI_ordType).
move => D f d0 d1 deq i.
by rewrite -> deq.
Qed.

Definition Prodi_fun D (f:forall i:I, D =-> O i) : D =-> prodI_ordType := Eval hnf in mk_fmono (prodi_fun_mon f).

End OrdProdI.

Lemma ordProdIAxiom : forall I:Type, @CatIProduct.axiom _ I (@prodI_ordType I) (@Proj I) (@Prodi_fun I).
move => I A X f. split.
- move => i. by apply fmon_eq_intro => x.
- move => m Z. apply fmon_eq_intro => x. split ; simpl => i.
  + specialize (Z i). by apply (proj1 Z x).
  + specialize (Z i). by apply (proj2 Z x).
Qed.

Canonical Structure ordProdIMixin := prodICatMixin ordProdIAxiom.
Canonical Structure ordProdICat := Eval hnf in prodICatType ordProdIMixin.

Section ProdICPO.

Variable I:Type.
Variable D:I -> cpoType.

Lemma prodi_cpo_axiom : CPO.axiom (fun (f : natO =-> prodI_ordType D) (i:I) => lub (Proj D i << f)).
move => c x n ; split ; clear.
- move => i. simpl. by rewrite <- (le_lub _ n).
- move => C i. apply lub_le => n. simpl. by apply C.
Qed.

Canonical Structure prodi_cpoMixin := @CpoMixin (prodI_ordType D) _ prodi_cpo_axiom.
Canonical Structure prodi_cpoType := Eval hnf in @CpoType (prodI_ordType D) prodi_cpoMixin.

Lemma Proj_cont i : continuous (@Proj I D i:ordCatType prodi_cpoType _).
move => i c. simpl. by apply: lub_le_compat.
Qed.

Definition PROJ i := Eval hnf in mk_fcont (Proj_cont i).

Lemma prod_fun_cont (D1:cpoType) (f:forall i:I, D1 =-> D i) :
   continuous (@Prodi_fun I _ D1 (fun i => (f i)) : ordCatType D1 prodi_cpoType).
move => D1 f c i.
simpl. rewrite (fcontinuous (f i)). by apply: lub_le_compat => n.
Qed.

Definition PRODI_fun D1 (f:forall i:I, D1 =-> D i) : D1 =-> prodi_cpoType :=
  Eval hnf in mk_fcont (prod_fun_cont f).

End ProdICPO.

Lemma cpoProdIAxiom : forall I:Type, @CatIProduct.axiom _ I (@prodi_cpoType I) (@PROJ I) (@PRODI_fun I).
move => I A X f. split.
- move => i. apply (proj1 (ordProdIAxiom f) i).
- move => m Z. by apply (proj2 (ordProdIAxiom f) m Z).
Qed.

Canonical Structure cpoProdIMixin := prodICatMixin cpoProdIAxiom.
Canonical Structure cpoProdICat := prodICatType cpoProdIMixin.

