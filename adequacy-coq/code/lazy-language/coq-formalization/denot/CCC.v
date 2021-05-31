(** * CCC: Cartesian closed categories *) 
Add LoadPath "./domain-theory".
Set Automatic Coercions Import.
Require Import Categories.
Set Implicit Arguments.
Unset Strict Implicit.

Module CartesianClosedCat.

  (** Exponential category with a terminal object *)
  Record mixin_of (C : expCat) : Type := Mixin {
    terminalM :> CatTerminal.mixin_of C
  }.

  Record class_of (T:Type) (M:T -> T -> setoidType) : Type := 
    Class {
        base :> CatExp.class_of M ; 
        ext :> mixin_of (CatExp.Pack base T) 
      }.

  Coercion base3 (T:Type) (M:T -> T -> setoidType) (c:class_of M) :
    CatTerminal.class_of M := CatTerminal.Class c.
  
  Structure cat : Type := 
    Pack {
        object :> Type; 
        morph :> object -> object -> setoidType ; 
        _ : class_of morph; 
        _ : Type
      }.

  Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c.
  
  Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
             (k : forall O (M: O -> O -> setoidType) 
                         (c : class_of M), K _ _ c) (cT:cat) :=
    let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
  
  Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
  Definition pack := let k T M c m := 
                         Pack (@Class T M c m) T in CatExp.unpack k.
  
  Definition catType (cT:cat) := Category.Pack (class cT) cT.
  Coercion catExpType (cT:cat) := CatExp.Pack (class cT) cT.
  Coercion catProdType (cT:cat) := CatProduct.Pack (class cT) cT.
  Coercion catTerminalType (cT:cat) := CatTerminal.Pack (class cT) cT.

End CartesianClosedCat.
Notation cartesianClosedCat := CartesianClosedCat.cat.
Notation cartesianClosedCatType := CartesianClosedCat.pack.
Canonical Structure CartesianClosedCat.catType.
Canonical Structure CartesianClosedCat.catExpType.
Canonical Structure CartesianClosedCat.catProdType.
Canonical Structure CartesianClosedCat.catTerminalType.
Open Scope C_scope.
