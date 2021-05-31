(**********************************************************************************
 * Finmap.v                                                                       *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * July 2010                                                                      *
 * Build with Coq 8.2pl1 plus SSREFLECT                                           *
 **********************************************************************************)

(* Finite maps with comparison on the domain *)

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

From mathcomp Require Export ssreflect ssrnat ssrbool seq eqtype.
From mathcomp Require Import ssrfun.
Require Import NSetoid MetricCore.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Comparison.

Definition axiomAS (T:Type) l := forall x y : T, reflect (x = y) (l x y && l y x).
Definition axiomCL T (l:T -> T -> bool) (comp:T -> T -> unit + bool) :=
    forall x y, ((comp x y == inl _ tt) = l x y && l y x) /\ (comp x y == inr _ true) = l x y && negb (l y x) /\ 
                 (comp x y == inr _ false) = l y x && negb (l x y).
Definition axiomT T l := forall x y z  : T, l x y && l y z ==> l x z.

Record mixin_of (T:Type) : Type := 
  Mixin { leq : T -> T -> bool;
          comp : T -> T -> unit + bool;
          _ : axiomAS leq;
          _ : axiomT leq;
          _ : axiomCL leq comp
  }.

Notation class_of := mixin_of (only parsing).
Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.

Definition eqop (T:type) (x y : T) := comp (class T) x y == inl _ tt.

Lemma eqP T : Equality.axiom (@eqop T).
case. move => T. case => l c A0 A1 A2 T'. unfold eqop. simpl.
move => x y. simpl. specialize (A0 x y). have A:=proj1 (A2 x y). simpl in A. rewrite <- A in A0. by apply A0.
Qed.

Lemma leq_refl (T:type) (x:T) : leq (class T) x x.
case. move => T. case. move => l c AS Tr CL X. simpl. move => x. case_eq (l x x) => L; first by [].
specialize (AS x x). rewrite L in AS. simpl in AS. by case AS.
Qed.

Lemma leq_trans (T:type) (x y z:T) : leq (class T) x y -> leq (class T) y z -> leq (class T) x z.
case. move => T. case. move => l c AS Tr CL X. simpl. move => x y z A B.
specialize (Tr x y z). rewrite -> A, -> B in Tr. rewrite implyTb in Tr. by apply Tr.
Qed.

Fixpoint sorted (T:type) (s:seq T) : bool :=
match s with
| nil => true
| x::s' => match s' with | nil => true | y::_ => leq (class T) x y && sorted s' end
end.

Lemma leq_seq_trans T x t s : leq (class T) x t -> all (leq (class T) t) s -> all (leq (class T) x) s.
move => T x t. elim ; first by [].
move => e s IH X. specialize (IH X). simpl. move => Y. rewrite (IH (proj2 (andP Y))). rewrite andbT.
apply (@leq_trans _ x t e). by rewrite X. by rewrite (proj1 (andP Y)).
Qed.

Lemma ltn_trans T x y t : leq (class T) x y -> leq (class T) t x -> ~~ eqop t x -> ~~ eqop t y.
move => T ; move: T (@eqP T). case => T. simpl. case => l c AS Tr CL X E. simpl. unfold eqop in E. simpl in E.
move => x y t L L'. unfold eqop. simpl. case_eq (c t y) ; last by case.
case. move => e. have e':c t y == inl bool tt by rewrite e.
have ee:=E _ _ e'. rewrite <- ee in L. specialize (AS t x). rewrite L in AS. rewrite L' in AS. simpl in AS.
specialize (E t x). simpl in E. case: E ; first by [].
have a:= elimT AS. specialize (a is_true_true). by rewrite a.
Qed.

Lemma ltn_seq_trans T x t s : leq (class T) x t -> negb (eqop x t) -> all (leq (class T) t) s -> 
  all (leq (class T) x) s && all (fun y => negb (eqop x y)) s.
move => T x t. elim ; first by [].
move => e s IH L N A. simpl in A. simpl. specialize (IH L N (proj2 (andP A))).
rewrite (leq_trans (y:=t) L) ; last by rewrite -> (proj1 (andP A)). simpl.
rewrite (leq_seq_trans L (proj2 (andP A))). simpl. rewrite (proj2 (andP IH)).
by rewrite (ltn_trans (proj1 (andP A)) L N).
Qed.

Lemma sorted_cons (T:type) (s:seq T) (x:T) : sorted (x::s) = all (leq (class T) x) s && sorted s.
move => T. elim ; first by [].
move => t s IH x. simpl @all.
apply trans_eq with (y:=leq (class T) x t && sorted (t::s)) ; first by []. rewrite (IH t). clear IH.
case_eq (leq (class T) x t) ; last by []. move => xt. simpl.
case_eq (all (leq (class T) t) s) ; last by simpl ; rewrite andbF.
move => ts. simpl. by rewrite (leq_seq_trans xt ts).
Qed.

Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.
Definition pack T c := @Pack T c T.

Coercion eqType cT := Equality.Pack (Equality.Mixin (@eqP cT)) cT.

Lemma comp_ne cT x y b : comp (class cT) x y = inr unit b -> negb (@eqop cT x y).
unfold eqop. move => cT x y b e. by rewrite e.
Qed.

End Comparison.

Notation compType := Comparison.type.
Notation CompType := Comparison.pack.
Notation CompMixin := Comparison.Mixin.

Canonical Structure Comparison.eqType.

Notation "[ 'compType' 'of' T 'for' cT ]" :=
    (@Comparison.repack cT (@Comparison.Pack T) T)
  (at level 0, format "[ 'compType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'compType' 'of' T ]" :=
    (Comparison.repack (fun c => @Comparison.Pack T c) T)
  (at level 0, format "[ 'compType'  'of'  T ]") : form_scope.

Definition comparison (T:compType) (x y:T) := Comparison.comp (Comparison.class T) x y.
Definition leq (T:compType) (x y:T) := Comparison.leq (Comparison.class T) x y.
Definition sorted (T:compType) (s:seq T) := Comparison.sorted s.

Lemma leq_trans (T:compType) (x y z:T) : leq x y -> leq y z -> leq x z.
move => T x y z E. by apply (Comparison.leq_trans E).
Qed.

Lemma leq_refl (T:compType) (x:T) : leq x x.
move => T x. by apply (Comparison.leq_refl).
Qed.

Lemma leq_seq_trans (T:compType) (x:T) t s : leq x t -> all (leq t) s -> all (leq x) s.
move => T x t s L A. by apply (Comparison.leq_seq_trans L A).
Qed.

Lemma ltn_trans (T:compType) (x y t:T) : leq x y -> leq t x -> t != x -> t != y.
move => T x y t L L' N. by apply (Comparison.ltn_trans L L' N).
Qed.

Lemma ltn_seq_trans (T:compType) (x t:T) s : leq x t -> x != t -> all (leq t) s -> 
  all (leq x) s && all (fun y => x != y) s.
move => T x t s L N A. by apply (Comparison.ltn_seq_trans L N A).
Qed.

Lemma sorted_cons (T:compType) (s:seq T) (x:T) : sorted (x::s) = all (leq x) s && sorted s.
move => T s x. by apply Comparison.sorted_cons.
Qed.

(** updated for 8.4 *)
Lemma comp_eq (T:compType) (x y:T) : (comparison x y == inl bool tt) = (x == y).
move => T x y. case_eq (comparison x y == inl bool tt) => E.
apply sym_eq. by apply E.
case_eq (x == y) => E' ; last by [].
case: T x y E E'. move => T. case => l c A0 A1 A2 T'. unfold comparison. simpl.
move => x y. have a:= (A0 x y). have A:=proj1 (A2 x y). move => F. simpl in A. rewrite F in A.
move => e. rewrite (eqP e) in A. by rewrite (introT (A0 y y) (refl_equal _)) in A.
Qed.

Lemma comp_leq (T:compType) (x y:T) : (comparison x y == inr unit true) = (leq x y && (x != y)).
move => T x y. case_eq (x == y) => E. have e:=comp_eq x y. rewrite E in e.
rewrite (eqP e). simpl. by rewrite andbF.

simpl. rewrite andbT. have e:(comparison x y != inl bool tt) by rewrite comp_eq ; rewrite E. clear E.
move: T x y e.
case => T. case => l c A0 A1 A2 T'. unfold comparison. unfold leq. simpl.
move => x y. have a:= (proj1 (proj2 (A2 x y))). simpl in a. rewrite a. clear a.
case_eq (l x y) => E ; last by []. simpl. case_eq (l y x) => L ; last by [].
specialize (A2 x y). rewrite E in A2. rewrite L in A2. simpl in A2. by rewrite (proj1 A2).
Qed.

Lemma comp_geq (T:compType) (x y:T) : (comparison x y == inr unit false) = (leq y x && (x != y)).
move => T x y. case_eq (x == y) => E. have e:=comp_eq x y. rewrite E in e.
rewrite (eqP e). simpl. by rewrite andbF.

simpl. rewrite andbT. have e:(comparison x y != inl bool tt) by rewrite comp_eq ; rewrite E. clear E.
move: T x y e.
case => T. case => l c A0 A1 A2 T'. unfold comparison. unfold leq. simpl.
move => x y. have a:= (proj2 (proj2 (A2 x y))). simpl in a. rewrite a. clear a.
case_eq (l y x) => E ; last by []. simpl. case_eq (l x y) => L ; last by [].
specialize (A2 x y). rewrite E in A2. rewrite L in A2. simpl in A2. by rewrite (proj1 A2).
Qed.

Lemma comp_neq (T:compType) (x y:T) b : comparison x y = inr _ b -> x != y.
move => T x y b E. by apply (Comparison.comp_ne E).
Qed.

Lemma comp_leqT (T:compType) (x y:T) : comparison x y = inr unit true -> leq x y.
case => T. case => l c AS Tr CL X. simpl. move => x y. have A:= (CL x y). unfold comparison. simpl. unfold leq. simpl.
move => E. rewrite E in A. simpl in A. have a:=proj1 (proj2 A). by case: (l x y) a.
Qed.

Lemma comp_leqF (T:compType) (x y:T) : comparison x y = inr unit false -> leq y x.
case => T. case => l c AS Tr CL X. simpl. move => x y. have A:= (CL x y). unfold comparison. simpl. unfold leq. simpl.
move => E. rewrite E in A. simpl in A. have a:=proj2 (proj2 A). by case: (l y x) a.
Qed.

Fixpoint compare_nat (m n : nat) : unit + bool :=
match m,n with
| O,O => inl _ tt
| S m, O => inr _ false
| O, S n => inr _ true
| S m, S n => compare_nat m n
end.

Lemma comp_natAS : Comparison.axiomAS ssrnat.leq.
move => x y. apply: (iffP idP) ; last by move => X ; rewrite X ; rewrite leqnn.
move => L. by apply (anti_leq L).
Qed.

Lemma nat_leqT : Comparison.axiomT ssrnat.leq.
move => x y z. case_eq (x <= y <= z) ; last by rewrite implyFb.
move => E. rewrite implyTb. by apply (ssrnat.leq_trans (proj1 (andP E)) (proj2 (andP E))).
Qed.

Lemma comp_natCL : Comparison.axiomCL ssrnat.leq compare_nat.
move => x y. simpl. elim: x y ; first by case.
move => x IH. case ; first by []. move => y. simpl. specialize (IH y).
rewrite (proj1 IH). rewrite (proj1 (proj2 IH)). by rewrite (proj2 (proj2 IH)).
Qed.

Canonical Structure nat_compMixin := CompMixin (comp:=compare_nat) comp_natAS nat_leqT comp_natCL.
Canonical Structure nat_compType := Eval hnf in CompType nat_compMixin.

Lemma map_map T T' T'' (f:T -> T') (g:T' -> T'') l : map g (map f l) = map (fun x => g (f x)) l.
move => T T' T'' f g. elim ; first by [].
move => e l IH. simpl. by rewrite IH.
Qed.

Section FinDom.
Variable T:compType.

Section Def.
Variable T':Type.

(*=FinDom *)
Record FinDom : Type := mk_findom 
{ findom_t : seq (T * T');
  findom_P : sorted (map (@fst T T') findom_t) &&
                     uniq (map (@fst T T') findom_t) }.
(*=End *)
Fixpoint findom_fun (f:seq (T * T')) (x:T) : option T' :=
match f with
| nil => None
| (x0,y) :: r => if x == x0 then Some y else findom_fun r x
end.

Definition findom_f f := findom_fun (findom_t f).

Definition dom f := map (@fst _ _) (findom_t f).
Definition codom f := map (@snd _ _) (findom_t f).

End Def.

Coercion findom_f : FinDom >-> Funclass.

Lemma findom_ext T' (f g:FinDom T') : dom f = dom g -> (forall x, x \in dom g -> f x = g x) -> g = f.
move => T'. case. unfold findom_f. unfold dom. simpl. move => f Pf. case. simpl. move => g Pg D C.
have e:f = g. elim: f g Pf Pg C D ; first by case.
case => c e f IH. case ; first by [].
case => c' e' g. simpl @map. do 2 rewrite sorted_cons.
move => A B C. case. move => E D. rewrite <- E. rewrite <- E in C, B. clear c' E.
specialize (IH g). rewrite  (proj2 (andP (proj1 (andP B)))) in IH. rewrite (proj2 (andP (proj1 (andP A)))) in IH.
simpl in A, B. rewrite  (proj2 (andP (proj2 (andP B)))) in IH. rewrite (proj2 (andP (proj2 (andP A)))) in IH.
specialize (IH is_true_true is_true_true). have E:= C c. rewrite in_cons in E. rewrite eq_refl in E.
specialize (E is_true_true). simpl in E. rewrite eq_refl in E. case: E => E. rewrite <- E. rewrite <- E in C. clear e' E.
rewrite IH ; [by [] | idtac | by []].
move => x X. specialize (C x). rewrite in_cons in C. have F:=proj1 (andP (proj2 (andP B))).
case_eq (x == c) => E ; first by rewrite <- (eqP E) in F ; rewrite X in F.
rewrite E in C. specialize (C X). simpl in C. rewrite E in C. by apply C.

move: C D Pg Pf. rewrite e. clear f e. move => C D Pg Pf. by rewrite (eq_irrelevance Pg Pf).
Qed.

Section Eq.
Variable Teq : eqType.
Definition findom_eq (f f':FinDom Teq) : bool := findom_t f == findom_t f'.

Lemma findom_eqP : Equality.axiom findom_eq.
move => f f'. apply: (iffP idP) ; last by move => e ; rewrite e ; apply eq_refl.
unfold findom_eq. case: f. move => l s. case: f'. simpl. move => l' s'.
move => X. move: s. rewrite (eqP X). clear. move => s. by rewrite (eq_irrelevance s s').
Qed.

Definition findom_leq (f f':FinDom Teq) : bool := all (fun x => f x == f' x) (dom f).

Lemma findom_leq_refl (f:FinDom Teq) : findom_leq f f.
case. unfold findom_leq. unfold dom. unfold findom_f. simpl. move => s P.
by apply (introT (@allP T _ (map (@fst _ _) s))).
Qed.

End Eq.

Variable T' : Type.

Lemma NoneP : sorted (T:=T) (map (@fst T T') [::]) && uniq (map (@fst T T') [::]).
by [].
Qed.

Definition fdEmpty : FinDom T' := mk_findom NoneP.

Fixpoint updpair (x:T * T') (l:seq (T * T')) : seq (T * T') :=
match l with
| nil => [:: x]
| y::yr => match comparison (fst x) (fst y) with inl _ => x::yr | inr true => x::y::yr | inr false => y::updpair x yr end
end.

Lemma findom_fun_notin T0 t s : t \notin map (@fst _ T0) s -> findom_fun s t = None.
move => T0 t s. elim: s ; first by [].
case => e2 e3 s IH. simpl. rewrite in_cons. rewrite negb_or. move => P.
specialize (IH (proj2 (andP P))). rewrite IH. rewrite <- if_neg. by rewrite (proj1 (andP P)).
Qed.

Lemma findom_upd (a:T') l s : findom_fun (updpair (l, a) s) l = Some a.
move => a l s. elim: s. simpl. by rewrite eq_refl.
- case => e0 e1 s IH. simpl. case_eq (comparison l e0) ; case => E.
  + simpl. by rewrite eq_refl.
  + simpl. by rewrite eq_refl.
  + simpl. have b:=comp_geq l e0. rewrite E in b. rewrite eq_refl in b. have c:=sym_eq b.
    have N:=proj2 (andP c). rewrite <- if_neg. rewrite N. by apply IH.
Qed.

Lemma findom_upd2 (a:T') x l s : x != l -> findom_fun (updpair (l, a) s) x = findom_fun s x.
move => a x l s P. elim: s. simpl. rewrite <- if_neg. by rewrite P.
case => e0 e1 s IH. simpl. case_eq (comparison l e0) ; case => E.
- have e:=comp_eq l e0. rewrite E in e. rewrite eq_refl in e.  simpl. rewrite <- (eqP (sym_eq e)).
  rewrite <- if_neg. rewrite P. rewrite <- if_neg. by rewrite P.
- simpl. rewrite <- if_neg. by rewrite P.
- simpl. case_eq (x == e0) ; first by []. move => E'. by apply IH.
Qed.

Lemma all_diff_notin (t:T) s : all (fun y : T => t != y) s == (t \notin s).
move => t. elim ; first by [].
move => t0 s IH. simpl. rewrite in_cons. rewrite negb_or. case_eq (t != t0) ; last by []. move => e. by apply IH.
Qed.

Lemma updpairP (x:T * T') f : sorted (T:=T) (map (@fst _ T') (updpair x (findom_t f))) &&
   uniq (map (@fst _ _) (updpair x (findom_t f))).
move => x. case. elim ; first by [].
move => t s IH. simpl @map. case_eq (comparison (fst x) (fst t)) ; case.
- move => e. have a:=comp_eq (fst x) t.1. rewrite e in a. rewrite (eq_refl) in a. by rewrite <- (eqP (sym_eq a)).
- move => C. clear IH. have L:=comp_leqT C. have N:=comp_neq C. clear C. simpl @map.
  do 3 rewrite sorted_cons. simpl @uniq. move => X. simpl @all. rewrite L. simpl.
  rewrite (proj1 (andP(proj1 (andP X)))). simpl. rewrite (proj2 (andP(proj2 (andP X)))). rewrite andbT.
  rewrite (proj1 (andP(proj2 (andP X)))). rewrite andbT. rewrite in_cons. rewrite (proj2 (andP (proj1 (andP X)))).
  rewrite andbT. rewrite (leq_seq_trans L (proj1 (andP (proj1 (andP X))))). simpl.
  rewrite negb_or. rewrite N. simpl. have a:= (proj1 (andP (proj2 (andP X)))).
  have b:=proj2 (andP (ltn_seq_trans L N (proj1 (andP (proj1 (andP X)))))).
  have c:=all_diff_notin x.1 (map (@fst _ _) s). rewrite b in c. by have d:=sym_eq (eqP c).
- move => C. have L:=comp_leqF C. have N:=comp_neq C. clear C. move => X. simpl in IH.
  simpl @map. rewrite sorted_cons in X. simpl in X. rewrite (proj2 (andP (proj1 (andP X)))) in IH.
  rewrite (proj2 (andP (proj2 (andP X)))) in IH. specialize (IH is_true_true).
  rewrite sorted_cons. rewrite (proj1 (andP IH)). rewrite andbT. simpl. rewrite (proj2 (andP IH)). rewrite andbT.
  have a:=proj1 (andP (proj1 (andP X))). have b:=proj1 (andP (proj2 (andP X))). clear X IH.
  elim: s a b. simpl. move => _ _. rewrite L. simpl. rewrite in_cons. rewrite negb_or. simpl. rewrite andbT.
    by rewrite (eq_sym t.1 x.1).
  case => t0 t0' s IH. move => X. simpl in X. specialize (IH (proj2 (andP X))).
  move => U. simpl in U. rewrite in_cons in U. rewrite negb_or in U. specialize (IH (proj2 (andP U))).
  simpl. case_eq (comparison x.1 t0) ; case.
  + simpl. rewrite L. simpl. rewrite (proj2 (andP X)). simpl.
    rewrite in_cons. rewrite negb_or. rewrite (proj2 (andP U)). move => _. rewrite andbT. by rewrite (eq_sym t.1 x.1).
  + simpl. move => C. have tr:=@leq_trans _ t.1 x.1 t0. rewrite (comp_leqT C) in tr. rewrite L in tr.
    specialize (tr is_true_true is_true_true). rewrite tr. simpl. rewrite L. simpl. rewrite (proj2 (andP X)). simpl.
    rewrite in_cons. rewrite negb_or. rewrite in_cons. rewrite negb_or. rewrite (proj1 (andP U)).
    rewrite (proj2 (andP U)). do 2 rewrite andbT. by rewrite (eq_sym t.1 x.1).
  + simpl. move => C. rewrite (proj1 (andP X)). simpl. rewrite (proj1 (andP IH)).
    simpl. rewrite in_cons. rewrite negb_or. rewrite (proj2 (andP IH)). by rewrite (proj1 (andP U)).
Qed.

Definition updMap (t:T) (t':T') (f:FinDom T') : FinDom T' := mk_findom (@updpairP (t,t') f).

Lemma updMap_simpl t t' f : updMap t t' f t = Some t'.
move => t t'. case => s f. unfold findom_f. simpl. clear f. elim:s ; first by simpl ; rewrite eq_refl.
move => e s IH. simpl. case_eq (comparison t e.1) ; case.
  + move => _. simpl. by rewrite eq_refl.
  + simpl. by rewrite eq_refl.
  + simpl. case: e. move => e0 e1. simpl. move => X. have a:=comp_geq t e0. rewrite X in a.
    rewrite eq_refl in a. have b:= sym_eq a. have f:=(proj2 (andP b)). case_eq (t == e0) => E ; first by rewrite E in f.
    by apply IH.
Qed.

Lemma updMap_simpl2 t t0 t' f : t0 != t -> updMap t t' f t0 = f t0.
move => t t0 t'. case => s f. unfold findom_f. simpl. clear f. move => ne. elim: s.
- simpl. case_eq (t0 == t) =>e ; last by []. by rewrite e in ne.
- move => e s IH. simpl. case_eq (comparison t e.1) ; case.
  + move => E. simpl. rewrite <- if_neg. rewrite ne. have te:=comp_eq t e.1. rewrite E in te. rewrite eq_refl in te.
    have te':=sym_eq te. rewrite (eqP te') in ne. clear E te te'. case: e ne. simpl. move => e0 e1 e. rewrite <- if_neg.
    by rewrite e.
  + simpl. rewrite <- if_neg. by rewrite ne.
  + simpl. by rewrite IH.
Qed.

Fixpoint rempair (x:T) (l:seq (T * T')) : seq (T * T') :=
match l with
| nil => [::]
| y::yr => match comparison x (fst y) with inl _ => yr | inr true => y::yr | inr false => y::rempair x yr end
end.

Lemma remMapP t f : sorted (T:=T) (map (@fst _ _) (rempair t (findom_t f))) &&
   uniq (map (@fst _ _) (rempair t (findom_t f))).
move => t. case. move => s P. simpl. elim: s P ; first by [].
case. move => t0 t0' s IH P. simpl.
case_eq (comparison t t0) ; case.
- move => C. simpl @map in P. rewrite sorted_cons in P. rewrite (proj2 (andP (proj1 (andP P)))). simpl.
  simpl in P. by rewrite (proj2 (andP (proj2 (andP P)))).
- by [].
- move => C. simpl @map. simpl @map in P. rewrite sorted_cons in P. simpl in P.
  rewrite (proj2 (andP (proj1 (andP P)))) in IH. rewrite (proj2 (andP (proj2 (andP P)))) in IH.
  specialize (IH is_true_true). rewrite sorted_cons. rewrite (proj1 (andP IH)). simpl. rewrite (proj2 (andP IH)).
  do 2 rewrite andbT. have a:=(proj1 (andP (proj1 (andP P)))). have b:=(proj1 (andP (proj2 (andP P)))). clear C P IH.
  elim: s a b ; first by []. case => e0 e1 s IH P Q. simpl. simpl in P. simpl in Q.
  case_eq (comparison t e0) ; case.
  + rewrite in_cons in Q. rewrite negb_or in Q. rewrite (proj2 (andP Q)). by rewrite (proj2 (andP P)).
  + simpl. rewrite Q. by rewrite P.
  + simpl. specialize (IH (proj2 (andP P))). rewrite in_cons in Q. rewrite negb_or in Q. specialize (IH (proj2 (andP Q))).
    rewrite in_cons. rewrite negb_or. rewrite (proj1 (andP IH)). rewrite (proj2 (andP IH)).
    rewrite (proj1 (andP Q)). by rewrite (proj1 (andP P)).
Qed.

Definition remMap (t:T) (f:FinDom T') : FinDom T' := mk_findom (@remMapP t f).

Lemma remMap_simpl t (f:FinDom T') : remMap t f t = None.
move => t. case. move => s P. unfold findom_f. simpl.
elim: s P ; first by [].
case => e0 e1 s IH. simpl @map. rewrite sorted_cons. move => P. simpl.
case_eq (comparison t e0) ;case.
- have Q:=proj1 (andP (proj2 (andP P))). clear IH P. move => C. have a:=comp_eq t e0. rewrite C in a. rewrite eq_refl in a.
  have b:=sym_eq a. rewrite <- (eqP b) in Q. clear a b C. by rewrite (findom_fun_notin Q).
- simpl. move => C. have a:=comp_leq t e0. rewrite C in a. rewrite eq_refl in a. have b:=sym_eq a.
  rewrite <- if_neg. rewrite (proj2 (andP b)).
  have c:=ltn_seq_trans (proj1 (andP b)) (proj2 (andP b)) (proj1 (andP (proj1 (andP P)))).
  rewrite (eqP (all_diff_notin _ _)) in c. by rewrite (findom_fun_notin (proj2 (andP c))).
- move => C. simpl in P.  rewrite (proj2 (andP (proj1 (andP P)))) in IH. rewrite (proj2 (andP (proj2 (andP P)))) in IH.
  simpl. rewrite IH ; last by []. rewrite <- if_neg. have a:=comp_geq t e0. rewrite C in a. rewrite eq_refl in a.
  have b:=sym_eq a. by rewrite (proj2 (andP b)).
Qed.

Lemma remMap_simpl2 t t' (f:FinDom T') : t' != t -> remMap t f t' = f t'.
move => t t'. case. move => s P. unfold findom_f. simpl. move => E.
elim: s P ; first by [].
case => e0 e1 s IH. simpl @map. rewrite sorted_cons. move => P. simpl.
case_eq (comparison t e0) ;case.
- have Q:=proj1 (andP (proj2 (andP P))). clear IH P. move => C. have a:=comp_eq t e0. rewrite C in a. rewrite eq_refl in a.
  have b:=sym_eq a. rewrite <- (eqP b) in Q. rewrite <- (eqP b). rewrite <- if_neg. by rewrite E.
- by [].
- move => C. simpl in P. simpl. rewrite (proj2 (andP (proj1 (andP P)))) in IH. rewrite (proj2 (andP (proj2 (andP P)))) in IH.
  simpl. by rewrite IH.
Qed.

Lemma map_pmap X Y (f:X -> Y) Z (g:Z -> option X) s : map f (pmap g s) = pmap (fun x => option_map f (g x)) s.
move => X Y f Z g. elim ; first by [].
move => t s IH. simpl. case_eq (g t). move => gt e. simpl. by rewrite IH. simpl. by rewrite IH.
Qed.

Lemma all_map_filter X Y (f:X -> Y) p g l : all p (map f l) -> all p (map f (filter g l)).
move => X Y f p g. elim ; first by []. move => t s IH P.
simpl. simpl in P. specialize (IH (proj2 (andP P))). case_eq (g t) ; last by [].
move => e. simpl. rewrite IH. by rewrite (proj1 (andP P)).
Qed.

Lemma sorted_map_filter X (f:X -> T) g l : sorted (map f l) -> sorted (T:=T) (map f (filter g l)).
move => X f g. elim ; first by []. move => t s IH. simpl @map. rewrite sorted_cons. move => P.
specialize (IH (proj2 (andP P))). 
case (g t) ; last by []. simpl @map ; rewrite sorted_cons. rewrite IH. by rewrite (all_map_filter _ (proj1 (andP P))).
Qed.

Lemma notin_map_filter X (Y:eqType) (f:X -> Y) p s x :x \notin map f s -> (x \notin map f (filter p s)).
move => X Y f p s x. elim: s ; first by [].
move => t s IH. simpl. rewrite in_cons. rewrite negb_or. move => P. specialize (IH (proj2 (andP P))).
case (p t) ; last by []. simpl. rewrite in_cons ; rewrite negb_or. rewrite IH. by rewrite (proj1 (andP P)).
Qed.

Lemma uniq_map_filter X (Y:eqType) (f:X -> Y) p l : uniq (map f l) -> uniq (map f (filter p l)).
move => X Y f p. elim ; first by []. move => t s IH. simpl. move => P. specialize (IH (proj2 (andP P))).
case (p t) ; last by []. simpl. rewrite IH. by rewrite (notin_map_filter _ (proj1 (andP P))).
Qed.

Lemma post_compP T0 (g : T' -> option T0) (f:FinDom T') : sorted (T:=T)
     (map (@fst _ _) (pmap (fun p : T * T' => option_map (fun r => (p.1,r)) (g p.2)) (findom_t f))) &&
   uniq (map (@fst _ _) (pmap (fun p : T * T' => option_map (fun r => (p.1,r)) (g p.2)) (findom_t f))).
move => T0 g. case. simpl. move => l. rewrite map_pmap.
have e:pmap (fun x => option_map (@fst _ _) (option_map [eta pair x.1] (g x.2))) l = (map (@fst _ T') (filter (fun p => g p.2) l)). elim: l ; first by []. case => e0 e1 s IH. simpl. case (g e1) ; simpl ; by rewrite IH.
rewrite e. clear e. move => P. rewrite (sorted_map_filter _ (proj1 (andP P))). simpl.
by rewrite (uniq_map_filter _ (proj2 (andP P))).
Qed.

Definition post_comp T0 (g : T' -> option T0) (f:FinDom T') : FinDom T0 := mk_findom (post_compP g f).

Definition option_bind Y Z (g:Y -> option Z) (y:option Y) : option Z :=
match y with | None => None | Some fx => g fx end.

Lemma post_comp_simpl T0 (g : T' -> option T0) (f:FinDom T') t : post_comp g f t = option_bind g (f t).
move => T0 g f t. case: f. unfold findom_f. simpl. elim ; first by [].
case => e0 e1 s IH. simpl @map. rewrite sorted_cons. move => P. simpl.
case_eq (t == e0) => e ; simpl. rewrite (eqP e). rewrite (eqP e) in IH. clear t e.
- case_eq (g e1) ; simpl ; first by rewrite eq_refl.
  move => ge. apply findom_fun_notin.
  have e:map (@fst _ _) (pmap (fun p : T * T' => option_map [eta pair p.1] (g p.2)) s) =
         map (@fst _ _) (filter (fun x => g x.2) s). clear P IH. elim: s ; first by []. clear.
    case => e0 e1 s. simpl. move => IH. by case (g e1) ; simpl ; rewrite IH.
  rewrite e. clear e. apply notin_map_filter. by apply (proj1 (andP (proj2 (andP P)))).
- rewrite (proj2 (andP (proj1 (andP P)))) in IH. simpl in P. rewrite (proj2 (andP (proj2 (andP P)))) in IH.
  case_eq (g e1) ; last by rewrite IH. move => ge e'. simpl. rewrite e. by rewrite IH.
Qed.

Lemma dom_post_comp T0 (g : T' -> option T0) (f:FinDom T') : dom (post_comp g f) = filter (fun x => isSome (option_bind g (f x))) (dom f).
move => T0 g. case. unfold findom_f. unfold dom. simpl. move => s Ps. have U:=proj2 (andP Ps). clear Ps.
elim: s U ; first by [].
case => c e f. simpl. move => IH. rewrite eq_refl. simpl. case_eq (g e).
- move => ge E. simpl. move => X.
  rewrite IH ; last by rewrite (proj2 (andP X)). f_equal. apply: eq_in_filter => x I.
  case_eq (x == c) => E' ; last by []. by rewrite (eqP E') in I ; rewrite I in X.
- move => E. simpl. move => X.
  rewrite IH ; last by rewrite (proj2 (andP X)). apply: eq_in_filter => x I.
  case_eq (x == c) => E' ; last by []. by rewrite (eqP E') in I ; rewrite I in X.
Qed.

Lemma findom_undef (f:FinDom T') x (P:x \notin dom f) : f x = None.
case => s P x C. unfold dom in C. simpl in C. by apply findom_fun_notin.
Qed.

Lemma findom_indom (f:FinDom T') t : (t \in dom f) = isSome (f t).
move => f t. case: f. unfold dom. unfold findom_f. simpl. move => s P.
elim: s P ; first by [].
case => t0 t0' s IH P. simpl. rewrite in_cons. case_eq (t == t0) => E ; first by [].
- simpl. apply IH. simpl @map in P. rewrite sorted_cons in P. simpl in P.
  rewrite (proj2 (andP (proj1 (andP P)))). by rewrite (proj2 (andP (proj2 (andP P)))).
Qed.

Lemma filter_some T0 (s:seq T0) : filter some s = s.
move => T0. elim ; first by [].
move => t s IH. simpl. by rewrite IH.
Qed.

Lemma dom_post_compS T0 (g : T' -> T0) (f:FinDom T') : dom (post_comp (fun x => Some (g x)) f) = dom f.
move => T0 g f. rewrite dom_post_comp. apply trans_eq with (y:=filter [eta some] (dom f)) ; last by rewrite filter_some.
apply: eq_in_filter => x I. rewrite findom_indom in I. by case: (f x) I.
Qed.

End FinDom.

Canonical Structure findom_eqMixin T T' := EqMixin (@findom_eqP T T').

(** updated for 8.4 *)
Canonical Structure findom_eqType T T' := Eval hnf in EqType _(findom_eqMixin T T').

Lemma leq_upd T (T':eqType) (f:FinDom T T') l a : l \notin (dom f) -> findom_leq f (updMap l a f).
move => T T' f l a. unfold findom_leq. unfold findom_f. unfold dom. simpl. case: f. simpl.
elim ; first by [].
case => e0 e1 s IH P. simpl @map in P. rewrite sorted_cons in P. simpl in P.
rewrite (proj2 (andP (proj1 (andP P)))) in IH. rewrite (proj2 (andP (proj2 (andP P)))) in IH.
move => N. simpl in N. rewrite in_cons in N. rewrite negb_or in N. specialize (IH is_true_true (proj2 (andP N))).
simpl @map. simpl. rewrite eq_refl. have NN:=proj1 (andP N).
case_eq (comparison l e0).
- case ; move => E. have b:=comp_eq l e0. rewrite E in b. by rewrite <- b in NN.
- case. move => E. simpl. rewrite <- if_neg. rewrite eq_refl. rewrite (eq_sym e0 l). rewrite NN. rewrite eq_refl. simpl.
  unfold is_true. rewrite <- IH. apply eq_all. move => x. simpl. case_eq (x == e0) => e.
  rewrite <- (eqP e) in NN. rewrite <- if_neg. rewrite (eq_sym x l). rewrite NN. rewrite eq_refl.
  rewrite findom_upd2 ; first by rewrite eq_refl. by rewrite (eq_sym x l).
  case_eq (x == l) => E'. rewrite (eqP E'). by rewrite findom_upd. rewrite findom_upd2 ; first by [].
  by rewrite E'.
- move => E. simpl. rewrite eq_refl. rewrite eq_refl. simpl. unfold is_true. rewrite <- IH. apply eq_all.
   move => x. simpl. case_eq (x == e0) => E' ; last by []. rewrite eq_refl. rewrite <- (eqP E') in NN.
   rewrite findom_upd2 ; first by rewrite eq_refl. by rewrite (eq_sym x l).
Qed.

Lemma fst_upd_eq (T:compType) T' T'' l (v:T') (v':T'') s s' : map (@fst _ _) s = map (@fst _ _) s' ->
  map (@fst _ _) (updpair (T:=T) (l, v) s) = map (@fst _ _) (updpair (T:=T) (l, v') s').
move => T T' T'' l v v'. elim; first by case.
case => e0 e1 s IH. simpl. case ; first by []. case => e2 e3 s'. simpl. move => P. have e:e0 = e2 by inversion P.
rewrite e. have ee:map (@fst _ _) s = map (@fst _ _) s' by inversion P. clear e0 e P.
case_eq (comparison l e2) ; first by simpl ; rewrite <- ee.
case => E. simpl. by rewrite ee.
simpl. by rewrite <- IH.
Qed.

Lemma dom_upd T T0 T1 l v v' (f:FinDom T T0) (f':FinDom T T1) : dom f == dom f' -> (dom (updMap l v f) == dom (updMap l v' f')).
move => T T0 T1 l v v'. case. move => s P. case => s' P'. unfold dom. simpl. clear P P'.
elim: s s' ; first by case.
move => t s IH. case ; first by [].
move => t' s'. simpl. move => P.
have e:t.1 = t'.1 /\ map (@fst _ _) s = map (@fst _ _) s' by have PP:=eqP P ; by inversion PP.
rewrite (proj1 e). case_eq (comparison l t'.1) ; first by simpl;  rewrite (proj2 e).
case ; simpl ; rewrite (proj1 e) ; first by rewrite (proj2 e). by rewrite <- (fst_upd_eq l v _ (proj2 e)).
Qed.

Lemma findom_dom_upd2 T T' (f:FinDom T T') l v : f l -> dom f == dom (updMap l v f).
move => T T' f l v D. case: f D. unfold dom. unfold findom_f. simpl. elim ; first by [].
case => e0 e1 s IH. simpl @map. rewrite sorted_cons. move => P. simpl.
case_eq (comparison l e0) ; case.
- move => E. have aa:=comp_eq l e0. rewrite E in aa. rewrite eq_refl in aa. rewrite <- aa. simpl.
  by rewrite (eqP (sym_eq aa)).
- simpl. move => L. have aa:=comp_leq l e0. rewrite L in aa. rewrite eq_refl in aa. 
  have b := proj2 (andP (sym_eq aa)). rewrite <- if_neg. rewrite b. have PP:=proj1 (andP (proj1 (andP P))).
  have c:= proj2 (andP (ltn_seq_trans (proj1 (andP (sym_eq aa))) b PP)).
  rewrite (eqP (all_diff_notin _ _)) in c. by rewrite (findom_fun_notin c).
- simpl. move => L. have aa:=comp_geq l e0. rewrite L in aa. rewrite eq_refl in aa. rewrite <- if_neg.
  rewrite (proj2 (andP (sym_eq aa))). move => X. rewrite (proj2 (andP (proj1 (andP P)))) in IH. simpl in P.
  rewrite (proj2 (andP (proj2 (andP P)))) in IH. specialize (IH is_true_true X). by rewrite (eqP IH).
Qed.

Lemma dom_updMap T T' (f:FinDom T T') l t : l \in dom f -> dom (updMap l t f) = dom f.
move => T T'. case => f Pf. unfold dom. simpl. move => l t. elim: f Pf ; first by [].
case => t0 t1 f IH Pf I. simpl in I. rewrite in_cons in I. case_eq (l == t0) => E.
- rewrite (eqP E). simpl. have A:= comp_eq t0 t0. rewrite (eq_refl) in A. by rewrite (eqP A).
- rewrite E in I. simpl in I. simpl.
  case_eq (comparison l t0) => b ; first by have B:=sym_eq (comp_eq l t0) ; rewrite E in B ; move => X ; rewrite X in B.
  case: b.
  + simpl. move => F. have A:=sym_eq (comp_leq l t0). rewrite F in A. rewrite eq_refl in A.
    simpl @map in Pf. rewrite sorted_cons in Pf. simpl in Pf. have B:=ltn_seq_trans (proj1 (andP A)) (proj2 (andP A)).
    specialize (B _ (proj1 (andP (proj1 (andP Pf))))). have BB:=proj2 (andP B).
    rewrite (eqP (all_diff_notin l (map (@fst _ _) f))) in BB. by rewrite I in BB.
  + move => A. simpl. f_equal. simpl @map in Pf. rewrite sorted_cons in Pf. simpl in Pf.
    rewrite (proj2 (andP (proj1 (andP Pf)))) in IH. rewrite (proj2 (andP (proj2 (andP Pf)))) in IH.
    by specialize (IH is_true_true I).
Qed.

Definition create_findom (T:compType) (T':Type) (l:seq T) (f:T -> option T') : (uniq l) -> (sorted l) -> FinDom T T'.
move => T T' l f U S. exists (pmap (fun x => option_map (fun y => (x,y)) (f x)) l).
have A:= (@pmap_uniq T _ _ id _ l U). rewrite map_pmap. rewrite -> A ; last by move => x ; simpl ; case (f x).
rewrite andbT. clear A. clear U.
elim: l S ; first by [].
move => t s IH S. rewrite sorted_cons in S. specialize (IH (proj2 (andP S))).
simpl. case (f t) ; last by apply IH.
move => t'. simpl @oapp. rewrite sorted_cons. rewrite IH. rewrite andbT. clear IH t'.
elim: s S ;first by []. move => x s IH A. rewrite sorted_cons in A. simpl in A.
rewrite (proj2 (andP (proj1 (andP A)))) in IH. rewrite (proj2 (andP (proj2 (andP A)))) in IH. specialize (IH is_true_true).
simpl. case (f x) ; last by apply IH. move => y. simpl. rewrite (proj1 (andP (proj1 (andP A)))). simpl.
by apply IH.
Defined.

Lemma create_findom_simpl (T:compType) (T':Type) (l:seq T) (f:T -> option T') (U:uniq l) (S:sorted l) :
  findom_t (create_findom f U S) = (pmap (fun x => option_map (fun y => (x,y)) (f x)) l).
by [].
Qed.

Definition create_findomF (T:compType) (X T':Type) (l:FinDom T X) (f:T -> option T') : FinDom T T'.
move => T X T'. case => l Pl f. by apply (create_findom f (proj2 (andP Pl)) (proj1 (andP Pl))).
Defined.

Lemma dom_create_findom (T:compType) T' (f:T -> option T') x U S :
   dom (@create_findom _ _ x f U S) = filter [eta f] x.
move => T T' f. unfold dom. move => x U S. rewrite create_findom_simpl.
rewrite pmap_filter. apply eq_filter => a. by case (f a).
move => a. simpl. by case (f a).
Qed.

Lemma dom_create_findomF (T:compType) T' T'' (f:T -> option T') (x:FinDom T T'') :
   dom (create_findomF x f) = filter [eta f] (dom x).
move => T T' T'' f x. case: x. simpl. move => x P. by rewrite dom_create_findom.
Qed.

Lemma create_findomF_simpl (T:compType) T' T'' (f:T -> option T') (x:FinDom T T'') i :
   create_findomF x f i = if i \in dom x then f i else None.
move => T T' T'' f x i. unfold findom_f. case: x => x P. simpl. unfold dom. simpl.
elim: x P ; first by [].
case => j x s IH. simpl @map. rewrite sorted_cons. simpl. move => P.
rewrite (proj2 (andP (proj1 (andP P)))) in IH. rewrite (proj2 (andP (proj2 (andP P)))) in IH. specialize (IH is_true_true).
case_eq (f j).
- move => t fj. simpl. rewrite in_cons. case_eq (i == j) => IJ ; first by rewrite <- (eqP IJ) in fj ; rewrite fj.
  simpl. by apply IH.
- move => fj. simpl. rewrite in_cons. rewrite IH. case_eq (i == j) => E ; last by [].
  simpl. rewrite <- (eqP E) in fj. rewrite fj. simpl. case_eq (i \in map (@fst _ _) s) => X ; by rewrite X.
Qed.


Section FinMap.

Variable T:compType.

Section SET.
Variable S:setoidType.

Lemma finmap_setoid_axiom : Setoid.axiom (fun f f' : FinDom T S => dom f = dom f' /\ forall t, f t =-= f' t ).
split ; last split.
- by move => f ; simpl ; split ; last by [].
- move => x y z ; simpl => X Y. split ; first by rewrite (proj1 X) ; rewrite (proj1 Y).
  move => t. rewrite -> (proj2 X t). by rewrite -> (proj2 Y t).
- move => x y ; simpl => X. split ; first by rewrite (proj1 X).
  move => t. by rewrite -> (proj2 X t).
Qed.

Canonical Structure findom_setoidMixin := SetoidMixin finmap_setoid_axiom.
Canonical Structure findom_setoidType := Eval hnf in SetoidType findom_setoidMixin.

End SET.

Lemma respect_domeq T' (f f':findom_setoidType T') : f =-= f' -> dom f = dom f'.
move => T'. case => s P. case => s' P'.
unfold dom. simpl. unfold tset_eq. simpl. unfold dom. simpl. by move => [A _].
Qed.

Section MET.

Variable M:metricType.

Lemma Pemp T' (x:T) (P:x \in map (@fst _ T') nil) : False.
move => T' x. by [].
Qed.

Fixpoint indom_app_fi T' (s:seq (T * T')) x (P:x \in map (@fst _ _) s) :=
match s as s0 return x \in map (@fst _ _) s0 -> T' with 
| nil => fun F => match Pemp F with end
| (a,b)::r => fun P => (match (x == a) as b return b || (x \in map (@fst _ _) r) -> T'
                        with true => fun _ => b
                           | false => fun P => @indom_app_fi _ r x P end) P
end P.

Definition indom_app T' (f:FinDom T T') x (P:x \in dom f) : T' := @indom_app_fi T' (findom_t f) x P.

Lemma indom_app_eq T' (f:FinDom T T') x (P:x \in dom f) : Some (indom_app P) = f x.
move => T'. case. move => s P x I. elim: s P I ; first by [].
case => a b s IH. simpl @map. simpl @uniq. unfold dom. simpl @map. move => P. unfold in_mem. simpl.
move => I. have X:= proj1 (andP P). rewrite sorted_cons in X.
have Y:sorted (map (@fst _ _) s) && uniq (map (@fst _ _) s). rewrite (proj2 (andP X)). simpl.
  by rewrite (proj2 (andP (proj2 (andP P)))).
specialize (IH Y). unfold dom in IH. simpl in IH.
case_eq (x == a) => A.
- move: I. unfold findom_f. simpl. move: A. clear. move => A. unfold indom_app. simpl. by rewrite A.
- unfold findom_f. unfold indom_app. move: I. simpl. rewrite A. simpl. move => I. specialize (IH I).
  unfold indom_app in IH. simpl in IH. by rewrite IH.
Qed.

Lemma indom_app_respect T' (f f': findom_setoidType T') x (P:x \in dom f) (P':x \in dom f') : f =-= f' -> indom_app P =-= indom_app P'.
move => T' f f' x P P' e. have X:Some (indom_app P) =-= Some (indom_app P') ; last by apply X.
do 2 rewrite indom_app_eq. clear P P'. case: f e => s P. case: f' => s' P'. move => e.
unfold tset_eq in e. simpl in e. by apply (proj2 e).
Qed.

Lemma findom_metric_respect2 n : setoid_respect2 (fun f f' : FinDom T M => match n with O => True | S _ =>
       dom f = dom f' /\ forall i (I:i \in dom f) (I':i \in dom f'), indom_app I = n = indom_app I' end).
case ; first by [].
move => n. split.
- move => f g h e. split => X.
  + split ; first by rewrite <- (proj1 X) ; rewrite (respect_domeq e).
    move => i I I'. have Ig: i \in dom g by rewrite (proj1 X).
    apply (Mrel_trans (proj2 (Mrefl _ _) (indom_app_respect I Ig (tset_sym e)) _)). clear I e h. by apply X.
  + split ; first by rewrite <- (proj1 X) ; rewrite (respect_domeq e).
    move => i I I'. have Ig: i \in dom h by rewrite (proj1 X).
    apply (Mrel_trans (proj2 (Mrefl _ _) (indom_app_respect I Ig e) _)). clear I e g. by apply X.
- move => f g h e. split => X.
  + split ; first by rewrite (proj1 X) ; rewrite (respect_domeq e).
    move => i I I'. have Ig: i \in dom g by rewrite (proj1 X) in I.
    refine (Mrel_trans _ (proj2 (Mrefl _ _) (indom_app_respect Ig I' (e)) _)). clear I' e h. by apply X.
  + split ; first by rewrite (proj1 X) ; rewrite (respect_domeq e).
    move => i I I'. have Ig: i \in dom h by rewrite (proj1 X) in I.
    refine (Mrel_trans _ (proj2 (Mrefl _ _) (indom_app_respect Ig I' (tset_sym e)) _)). clear I' e g. by apply X.
Qed.

Lemma findom_metric_axiom : Metric.axiom (fun n => (fun f f' : FinDom T M => match n with O => True | S _ =>
       dom f = dom f' /\ forall i (I:i \in dom f) (I':i \in dom f'), indom_app I = n = indom_app I' end)).
move => n x y z ; split ; last split ; last split ; last split ; clear.
- split => X.
  + simpl in X. split ; have A:=proj1 (X 1) ; first by [].
    move => t. case_eq (t \in dom x) => D.
    * have D':=D. rewrite A in D'. apply: (proj1 (Mrefl _ _)). case  ; first by []. move => n.
      specialize (X (S n)). simpl in X. have Y:=proj2 X _ D D'. clear X.
      rewrite <- (indom_app_eq D). simpl. rewrite <- (indom_app_eq D'). by apply Y.
    * rewrite (findom_undef (negbT D)). rewrite A in D. by rewrite (findom_undef (negbT D)).
  + case ; first by []. move => n. simpl. split ; first by apply (respect_domeq  X).
    move => i I I'. by apply (proj2 (Mrefl _ _) (indom_app_respect I I' X)).
- case: n ; first by []. move => n X. split ; first by apply (sym_eq (proj1 X)).
  move => i I I'. have A:=proj2 X i I' I. by apply Msym.
- case: n ; first by []. move => n [X X'] [Y Y']. split ; first by rewrite X.
  move => i I I'. have Iy:=I. rewrite X in Iy.
  by apply (Mrel_trans (X' _ I Iy) (Y' _ Iy I')).
- case: n ; first by []. move => n X. split ; first by apply (proj1 X). move => i I I'.
  have Y:=proj2 X _ I I'. by apply Mmono.
- by [].
Qed.

Canonical Structure findom_metricMixin := MetricMixin findom_metric_axiom.
Canonical Structure findom_metricType := Eval hnf in MetricType findom_metricMixin.

Lemma findom_f_nonexp (f f':findom_metricType) n x : f = n = f' -> f x = n = f' x.
move => f f'. case ; first by [].
move => n x [E P]. case_eq (x \in dom f) => D.
- have D':=D. rewrite E in D'. specialize (P x D D'). rewrite <- (indom_app_eq D).
  have A: f' x = n.+1 = Some (indom_app D') by rewrite (indom_app_eq D').
  refine (Mrel_trans _ (Msym A)). by apply P.
  have DD:=negbT D. rewrite (findom_undef DD). rewrite E in DD. by rewrite (findom_undef DD).
Qed.

Lemma findom_sapp_respect T' (x:T) : setoid_respect (fun f:findom_setoidType T' => f x).
move => T' x f f' e. by apply (proj2 e x).
Qed.

Definition findom_sapp T' (x:T) : findom_setoidType T' =-> option_setoidType T' :=
  Eval hnf in mk_fset (findom_sapp_respect x).

Lemma findom_sapp_ne (x:T) : nonexpansive (findom_sapp _ x).
move => x n f f' e. by apply: findom_f_nonexp.
Qed.

Definition findom_napp (x:T) : findom_metricType =-> option_metricType M :=
  Eval hnf in mk_fmet (findom_sapp_ne x).

End MET.

Section CMET.
Variable M:cmetricType.

Lemma findom_chain_dom x n (c:cchain (findom_metricType M)) : x \in dom (c 1) -> x \in dom (c n.+1).
move => x. elim ; first by [].
move => n IH c X. specialize (IH (cutn 1 c)). simpl in IH. do 2 rewrite -> addSn, -> add0n in IH.
apply IH. clear IH. have C:=cchain_cauchy c. specialize (C 1 1 2 (ltnSn _) (ltnW (ltnSn _))).
by rewrite (proj1 C) in X.
Qed.

Definition findom_chainx (c:cchain (findom_metricType M)) x (P:x \in dom (c 1)) : cchain M.
move => c x P. exists (fun n => @indom_app _ (c n.+1) _ (findom_chain_dom n P)).
case ; first by [].
move => n i j l l'. simpl.
have X: Some (indom_app (findom_chain_dom i P)) = n.+1 = Some (indom_app (findom_chain_dom j P)) ; last by apply X.
do 2 rewrite indom_app_eq. have a:= (@cchain_cauchy _ c n.+1 i.+1 j.+1 (ltnW l) (ltnW l')).
by apply findom_f_nonexp.
Defined.

Lemma mem_cons x y (s:seq T) : x \in s -> x \in (y::s).
move => x y s I. rewrite in_cons. rewrite I. by rewrite orbT.
Qed.

Fixpoint indom_app_map T' P' (f:forall x, P' x -> T') (s:seq T) (I:forall x, x \in s -> P' x) : seq (T * T') :=
match s as s0 return (forall x, x \in s0 -> P' x) -> seq (T * T') with 
| nil => fun _ => nil
| cons x rs => fun P => (x,f x (P x (mem_head x rs))) :: (@indom_app_map _ P' f rs (fun y X => P _ (mem_cons x X)))
end I.

Lemma list_fst_map T' P' (f:forall x, P' x -> T') (s:seq T) (I:forall x, x \in s -> P' x) :
  map (@fst _ _) (indom_app_map f I) = s.
move => T' P' f. elim ; first by [].
move=> t s IH I. simpl. specialize (IH (fun (y : T) (X : y \in s) => I y (mem_cons t X))).
f_equal. by apply IH.
Qed.

Definition findom_map T' T'' (m:FinDom T T') (f:forall x, x \in dom m -> T'') : FinDom T T''.
move => T' T'' m f. exists (@indom_app_map T'' (fun x => x \in dom m) f (dom m) (fun x X => X)).
case: m f => s P f. rewrite list_fst_map. unfold dom. by apply P.
Defined.

Lemma dom_findom_map T' T'' (m:FinDom T T') (f:forall x, x \in dom m -> T'') : dom m = dom (findom_map f).
move => T' T'' m f. have A:=list_fst_map f (fun x => id). by rewrite <- A.
Qed.

Definition findom_lub (c:cchain (findom_metricType M)) : findom_metricType M :=
  @findom_map _ _ (c 1) (fun x X => umet_complete (@findom_chainx c x X)).

(** updated for 8.4 *)
Lemma ff (P:T -> nat -> Prop) (A:forall x n m, n <= m -> P x n -> P x m) (s:seq T) :
  (forall x, x \in s -> exists m, P x m) -> exists m, forall x, x \in s -> P x m.
move => P A. elim ; first by move => X; exists 0.
move => t s IH X. specialize (IH (fun x A => X x (mem_cons t A))). destruct IH as [m IH].
have X':=X t (mem_head t _). destruct X' as [m' Pm']. exists (maxn m m'). move => x I.
rewrite in_cons in I. case_eq (x == t) => E.
- rewrite (eqP E). apply: (A _ _ _ _ Pm'). apply leq_maxr. 
- rewrite E in I. simpl in I. specialize (IH _ I). apply: (A _ _ _ _ IH). 
apply leq_maxl.
Qed.

Lemma findom_fun_map T' P (f:forall x, P x -> T') (s:seq T) (I:forall x, x \in s -> P x) x (I':x \in s) :
   findom_fun (@indom_app_map _ P f s I) x = Some (f x (I _ I')).
move => T' P f. elim ; first by [].
move => t s IH I x I'. simpl. case_eq (x == t) => E. move: I'. rewrite (eqP E). move => I'.
 by rewrite (eq_irrelevance (mem_head t s) I').
specialize (IH (fun (y : T) (X : y \in s) => I y (mem_cons t X))). specialize (IH x).
have I0:= I'. rewrite in_cons in I0. rewrite E in I0. simpl in I0. specialize (IH I0). rewrite IH.
by rewrite (eq_irrelevance (mem_cons t I0) I').
Qed.

Lemma findom_map_app T' T'' (m:FinDom T T') x (I:x \in dom m) (f:forall x, x \in dom m -> T'') :
   findom_map f x = Some (f x I).
move => T' T''. case. move => s P. unfold findom_f. simpl. unfold dom. simpl.
move => x I f. apply (findom_fun_map f (fun x => id) I).
Qed.

Lemma findom_lubP (c:cchain (findom_metricType M)) : mconverge c (findom_lub c).
move => c. unfold findom_lub. case ; first by exists 0. move => n.
have A:exists m, forall x, x \in dom (c 1) -> forall (X: x \in dom (c 1)) i, m < i -> c i x = n.+1 = Some (umet_complete (findom_chainx X)).
apply (@ff (fun x m => forall (X:x \in dom (c 1)) i, m < i -> c i x = n.+1 = Some (umet_complete (findom_chainx X)))).
clear. move => x j i A Y X k L. apply Y. by apply (@ssrnat.leq_ltn_trans _ _ _ A L).
move => x I. destruct (cumet_conv (findom_chainx I) n.+1) as [m P].
exists m. move => X. case ; first by []. move => i L. specialize (P i L). simpl in P.
rewrite <- (indom_app_eq (findom_chain_dom i I)).
apply: (Mrel_trans P). apply umet_complete_extn. move=> j. simpl.
have A:Some (indom_app (findom_chain_dom j I)) = n.+1 = Some (indom_app (findom_chain_dom j X)) ; last by apply A.
rewrite (indom_app_eq (findom_chain_dom j I)). by rewrite (indom_app_eq (findom_chain_dom j X)).
destruct A as [m A]. exists m.+1. case ; first by []. move => i L. split. rewrite <- dom_findom_map.
have B:=cchain_cauchy c. specialize (B 1 i.+1 1 (ltn0Sn i) (ltn0Sn _)). apply (proj1 B).
move => x I I'. have X:Some (indom_app I) = n.+1 = Some (indom_app I') ; last by apply X.
rewrite (indom_app_eq I). rewrite (indom_app_eq I').
have J:x \in dom (c 1). have J:=cchain_cauchy c. specialize (J 1 i.+1 1 (ltn0Sn _) (ltn0Sn _)). have X:= (proj1 J).
rewrite X in I. by [].
 specialize (A x J J i.+1 L). apply (Mrel_trans A).
by rewrite -> (findom_map_app J).
Qed.

Canonical Structure findom_cmetricMixin := CMetricMixin findom_lubP.
Canonical Structure findom_cmetricType := Eval hnf in CMetricType findom_cmetricMixin.

End CMET.

End FinMap.

