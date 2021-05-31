Add Rec LoadPath "." as Top.
Add LoadPath "../denot/domain-theory".

Require Import Utils.
Require Import Program.

Set Automatic Coercions Import.
Set Implicit Arguments.

Require Import Syntax.
Require Import BOp.
Require Import List.
Require Import Ensembles.
Require Import Basics.
Require Import ZArith.

Require Import DomainStuff.
Require Import PredomAll.
Require Import uniirec.

Include RD.

(** * Language Semantics *)

(** Semantics of a terminating types *)
Fixpoint t_ty_denot (ty : type) : cpoType :=
  let ty_denot (ty : type) : cpoType := (t_ty_denot ty) _BOT
  in match ty with
  | tunit => One
  | tint  => int_cpoType
  | a ⇾ b => ty_denot a -=> ty_denot b
  | a ⨱ b => ty_denot a * ty_denot b
  end
.

Definition ty_denot (ty : type) : cpoType := (t_ty_denot ty) _BOT.

(** Semantics of a context *)
Fixpoint ctx_denot (c : ctx) : cpoType :=
  match c with
    nil => One
  | a :: c => ty_denot a * ctx_denot c
  end.

(** Environment projection on a variable *)
Fixpoint lookup ctx a (v : var ctx a) : ctx_denot ctx =-> ty_denot a :=
  match v in var ctx a return ctx_denot ctx =-> ty_denot a with
    zvar _ _ => FST _ _
  | svar _ _ _ v => lookup v << SND _ _
  end.

Definition IfZIntTy (A B : cpoType) :
  (A -=> int_cpoType _BOT) -=> (A -=> B _BOT) -=> (A -=> B _BOT) -=> A -=> B _BOT
  := exp_fun (exp_fun (exp_fun (
  kleisli ev
  <<
  (RStrength _ _)
  <<
  kleisli (eta << IfZInt _ _) >< Id
  <<
  (LStrength _ _) >< Id
  <<
  <| <| <| pi2 << pi1 << pi1, pi2 << pi1 |>
      , ev << <| pi1 << pi1 << pi1, pi2 |>
      |>
   , pi2 (A:=((A -=> int_cpoType _BOT) * (A -=> B _BOT) * (A -=> B _BOT))) (B:=A)
   |>))).

Arguments IfZIntTy [A B].

Definition CProd_fun (D1 D2 D3 : cpoType) :
  (D1 -=> D2 _BOT) * (D1 -=> D3 _BOT) =-> (D1 -=> (D2 _BOT * D3 _BOT) _BOT)
  := exp_fun (eta << (<|ev << <|pi1 << pi1,pi2|>,ev << <|pi2 << pi1,pi2|>|>)).
Arguments CProd_fun [D1 D2 D3].

Definition cprod_fun (D1 D2 D3 : cpoType) :
  (D1 -=> D2 _BOT) =-> (D1 -=> D3 _BOT) -=> (D1 -=> (D2 _BOT * D3 _BOT) _BOT)
  := @CCURRY (D1 -=> D2 _BOT) (D1 -=> D3 _BOT) (D1 -=> (D2 _BOT * D3 _BOT) _BOT)
            (@CProd_fun D1 D2 D3).
Arguments cprod_fun [D1 D2 D3].

Definition AbsTyTrans (A B C : cpoType)
  : (((A * B -=> C) * B) * A) -=> C
  :=
    ev << <| pi1 , <| pi2 << pi2 , pi1 << pi2 |> |>
       << <| pi1 << pi1 , <| pi2 << pi1 , pi2 |> |>.
Arguments AbsTyTrans [A B C].

Definition AbsTy (A B C: cpoType)
  : ((A * B) -=> C) -=> (B -=> (A -=> C) _BOT)
  := (exp_fun (eta << ev << @CCURRY B A C >< @Id _ B)) << SwapArgs.
Arguments AbsTy [A B C].

Definition AppTy (A B C: cpoType)
  : (A -=> (B -=> C _BOT) _BOT) -=> (A -=> B) -=>
    (A -=> C _BOT)
  := exp_fun (exp_fun (
    (kleisli ev)
    <<
    (RStrength _ _)  
    <<
    <| ev << <|pi1 << pi1, pi2|> , ev << <| pi2 << pi1, pi2|> |>)).
Arguments AppTy [A B C].

Definition SwapAppTy (A B C: cpoType)
  : (A -=> B) -=> (A -=> (B -=> C _BOT) _BOT) -=>
    (A -=> C _BOT)
  := CURRY (SwapArgs (UNCURRY AppTy)).
Arguments SwapAppTy [A B C].

Definition LetTy (A B C: cpoType)
  : ((A _BOT * B) -=> C _BOT) -=> (B -=> A _BOT) -=> (B -=> C _BOT)
  := exp_fun (exp_fun(
         AbsTyTrans << <| <|pi1 << pi1, pi2|> , ev << <| pi2 << pi1, pi2|> |>)).
Arguments LetTy [A B C].

Definition IntOpTy (A : cpoType) (op : Z -> Z -> Z) :
  (A -=> int_cpoType _BOT) -=> (A -=> int_cpoType _BOT) -=>
  (A -=> int_cpoType _BOT)
    := exp_fun (exp_fun (
                   kleisli (eta << SimpleBOp op) << uncurry (Smash _ _)
                   << ev >< ev
                   << <| pi1 >< pi1, pi2 >< pi2|> << Id >< <| Id, Id |>)
                 ).
Arguments IntOpTy [A] _.

(** Set-theoretic denotational semantics *)

Reserved Notation "⟦ t ⟧" (at level 1, no associativity).

Fixpoint term_denot ctx a (t : term ctx a) : ctx_denot ctx =-> ty_denot a :=
  match t in term _ a return ctx_denot ctx =-> ty_denot a with
  | term_unit           => eta << @terminal_morph cpoTerminalType (ctx_denot ctx)
  | term_int n          => eta << const (ctx_denot ctx) n
  | term_var _ v        => lookup v
  | term_abs _ _ t      => AbsTy ⟦ t ⟧
  | term_app _ _ t v    => AppTy ⟦ t ⟧ (lookup v)
  | term_let _ _ t t'   => LetTy ⟦ t' ⟧ (FixF ⟦ t ⟧)
  | term_bop bop t t'   => IntOpTy (semZBOp bop) ⟦ t ⟧ ⟦ t' ⟧
  | term_ifz _ t t' t'' => IfZIntTy ⟦ t ⟧ ⟦ t' ⟧ ⟦ t'' ⟧
  | term_pair _ _ t t'  => eta << <| ⟦ t ⟧ , ⟦ t' ⟧ |>
  | term_fst _ _ v      => kleisli (FST _ _) << lookup v
  | term_snd _ _ v      => kleisli (SND _ _) << lookup v
  end
where "⟦ t ⟧" := (term_denot t).

Lemma nth_error_nil :
  forall n A, @nth_error A nil n = None.
Proof.
  intros n A.
  case n ; simpl ; auto.
Qed.

Lemma none_is_not_some:
  forall A (a : A), None <> Some a.
Proof.
  intros. discriminate.
Qed.

(** Find a variable type inside a given context *)
Fixpoint lookup_nat (n : nat) ctx a :
  nth_error ctx n = Some a -> ctx_denot ctx -> ty_denot a.
  refine (
      match ctx return nth_error ctx n = Some a -> ctx_denot ctx -> ty_denot a with
      | nil =>
        match n as n0 return (nth_error nil n0 = Some a -> ctx_denot nil -> ty_denot a) with
          0 => fun _ => _
        | S n => fun _ => _
        end       
      | a' :: ctx' =>
        match n as n0 return (nth_error (a' :: ctx') n0 = Some a -> ctx_denot  (a' :: ctx') -> ty_denot a) with
          0 => fun q => match q with
                      Logic.eq_refl => fst
                    end
        | S n' => fun _ => fun ρ => lookup_nat n' ctx' a _ (snd ρ)
        end
      end
    ).
  simpl in *.
  set (X := @none_is_not_some _ a).
  contradiction.
  set (X := @none_is_not_some _ a).
  contradiction.
  auto.
Defined.

Definition AppTy_ρ (A B : cpoType) : (A -=> B _BOT) _BOT -=> A -=> B _BOT
  := exp_fun (kleisli ev << (RStrength _ _)).
Arguments AppTy_ρ [A B].

Lemma sem_term_app_Eq' : forall (c : ctx) (θ1 θ2 : type)
                           (t : term c (θ1 ⇾ θ2)) (v : var c θ1)
                           (ρ : ctx_denot c),
    ⟦ term_app c θ1 θ2 t v ⟧ ρ =-= ((AppTy ⟦ t ⟧) (lookup v)) ρ.
Proof.
  auto.
Qed.

Lemma sem_term_app_Eq : forall (c : ctx) (θ1 θ2 : type) (v : var c θ1)
                          (d : ctx_denot c =-> ty_denot (θ1 ⇾ θ2))
                          (ρ : ctx_denot c),
    ((AppTy d) (lookup v)) ρ =-= AppTy_ρ (d ρ) (lookup v ρ).
Proof.
  auto.
Qed.

Lemma AppTy_Prop : forall (c : ctx) (θ1 θ2 : type) (v : var c θ1)
                          (d : ctx_denot c =-> ty_denot (θ1 ⇾ θ2)),
    AppTy d (lookup v) =-= SwapAppTy (lookup v) d.
Proof.
  auto.
Qed.

Lemma SmashValVal :
  forall (A B : cpoType) (d1 : A _BOT) (d2 : B _BOT) (d1d2 : A * B),
    Smash _ _ d1 d2 =-= Val d1d2 ->
    exists (d1' : A) (d2' : B),
      d1 =-= eta d1' /\ d2 =-= eta d2' /\ eta (d1', d2') =-= eta d1d2.
Proof.
  intros A B d1 d2 d1d2 H.
  unfold Smash in H.
  apply Operator2Val in H.
  auto.
Qed.

Lemma AppTyValVal :
  forall (θ1 θ2 : type)
    (f : ty_denot (θ1 ⇾ θ2)) (d : ty_denot θ1) (fd : t_ty_denot θ2),
    (AppTy_ρ f) d =-= eta fd ->
    exists f', f =-= eta f' /\ f' d =-= eta fd.
Proof.
  fold t_ty_denot. intros θ1 θ2 f d fd H.
  unfold AppTy_ρ in H. fold t_ty_denot in *.
  simpl in H. unfold id in H.
  apply kleisliValVal in H.
  destruct H as [ff [? ?]].
  apply SmashValVal in H.
  inversion H as [f' [d' [? [? ?]]]].
  exists f'. split. auto. rewrite <- H0.
  apply vinj in H3. rewrite <- H3.
  simpl. apply vinj in H2. rewrite <- H2.
  auto.
Qed.

Lemma AppTyFVal :
  forall (θ1 θ2 : type) (f : t_ty_denot (θ1 ⇾ θ2)) (d : ty_denot θ1),
    (AppTy_ρ (eta f)) d =-= f d.
Proof.
  intros θ1 θ2 f d.
  simpl. fold t_ty_denot. unfold id. simpl.
  assert ((Smash _ _ (Val f)) (Val d) =-= Val (f,d)).
  by rewrite -> Smash_ValVal.
  rewrite -> H. clear H.
  by rewrite -> kleisliVal.
Qed.

Lemma BOpTyValVal' : forall (c : ctx) (bop : BOp)
                       (fd fd' : ctx_denot c =-> ty_denot tint)
                       (ρ : ctx_denot c)
                       (bopv : int_cpoType),
    IntOpTy (semZBOp bop) fd fd' ρ =-= eta bopv ->
    exists d d',
    fd ρ =-= Val d /\ fd' ρ =-= Val d' /\ semZBOp bop d d' = bopv.
Proof.
  intros c bop fd fd' ρ bopv H; simpl in H. unfold id in H.
  apply kleisliValVal in H. inversion H as [dp [? ?]].
  simpl in *. apply vinj in H1.
  apply SmashValVal in H0.
  inversion H0 as [d [d' [? [? ?]]]].
  simpl in *. apply vinj in H4. inversion H4. simpl in *.
  inversion H5. inversion H7. inversion H8.
  rewrite <- H9 in H1. rewrite <- H10 in H1.
  exists d, d'. split. auto. split. auto. auto. apply H1.
Qed.

Lemma BOpTyValVal : forall c bop t t' ρ (bopv : int_cpoType),
    ⟦ term_bop c bop t t' ⟧ ρ =-= eta bopv ->
    exists d d',
    ⟦ t ⟧ ρ =-= Val d /\  ⟦ t' ⟧ ρ =-= Val d' /\ semZBOp bop d d' = bopv.
Proof.
  intros c bop t t' ρ bopv H.
  apply BOpTyValVal'. auto.
Qed.

Lemma IfZSem_prop :
  forall (θ : type) (c : ctx) (d : int_cpoType)
    (d' d'' : ctx_denot c -=> ty_denot θ) (ρ : ctx_denot c),
    (IfZSemInt d' d'' d) ρ = IfZSemInt (d' ρ) (d'' ρ) d.
Proof.
  intros θ c d d' d'' ρ.
  destruct d. auto. auto. auto.
Qed.

Lemma IfZTyValVal' : forall (c : ctx) (θ : type)
                       (d : ctx_denot c =-> ty_denot tint)
                       (d' d'' : ctx_denot c =-> ty_denot θ)
                       (ρ : ctx_denot c)
                       (ifzv : t_ty_denot θ),
    IfZIntTy d d' d'' ρ =-= eta ifzv ->
    exists (dt : t_ty_denot tint),
      d ρ =-= eta dt /\ (IfZSemInt d' d'' dt) ρ =-= eta ifzv.
Proof.
  intros c θ d d' d'' ρ ifzv H.
  simpl in H. unfold id in H.
  apply kleisliValVal in H. destruct H as [da [? ?]].
  apply SmashValVal in H. destruct H as [da' [da'' [? [? ?]]]].
  apply kleisliValVal in H. destruct H as [dprod [? ?]].
  apply SmashValVal in H. destruct H as [dp [dp' [? [? ?]]]].
  apply vinj in H3. apply vinj in H1. apply vinj in H2.
  apply vinj in H5. apply vinj in H. rewrite <- H in H5.
  rewrite <- H5 in H3. simpl in H3. rewrite <- H1 in H2.
  rewrite <- H3 in H2. rewrite <- H2 in H0.
  exists dp'. auto.
Qed.

Lemma IfZTyValVal : forall c θ t t' t'' ρ ifzv,
    ⟦ term_ifz c θ t t' t'' ⟧ ρ =-= eta ifzv ->
    exists dt,
      ⟦ t ⟧ ρ =-= eta dt /\ (IfZSemInt ⟦ t' ⟧ ⟦ t'' ⟧ dt) ρ =-= eta ifzv.
Proof.
  intros c θ t t' t'' ρ ifzv H.
  apply IfZTyValVal'. auto.
Qed.

Lemma IfZSemInt_cont : forall (A B : cpoType)
                         (d : int_cpoType) (d' d'' : A -=> B) (ρ : A),
    IfZSemInt (d' ρ) (d'' ρ) d =-= (IfZSemInt d' d'' d) ρ.
Proof.
  intros A B d d' d'' ρ.
  destruct d.
    by simpl.
    by simpl.
    by simpl.
Qed.

Lemma FstTyValVal : forall c θ1 θ2 t ρ fstv,
    ⟦ term_fst c θ1 θ2 t ⟧ ρ =-= eta fstv ->
    exists (d' : ty_denot θ2), lookup t ρ =-= Val (Val fstv, d').
Proof.
  intros c θ1 θ2 t ρ fstv H.
  simpl in H. fold t_ty_denot in H.
  apply kleisliValVal in H. destruct H as [d [? ?]].
  destruct d. simpl in *. exists s0. rewrite -> H.
  apply Val_eq_compat. rewrite -> H0. auto.
Qed.

Lemma SndTyValVal : forall c θ1 θ2 t ρ sndv,
    ⟦ term_snd c θ1 θ2 t ⟧ ρ =-= eta sndv ->
    exists (d : ty_denot θ1), lookup t ρ =-= Val (d, Val sndv).
Proof.
  intros c θ1 θ2 t ρ fstv H.
  simpl in H. fold t_ty_denot in H.
  apply kleisliValVal in H. destruct H as [d [? ?]].
  destruct d. simpl in *. exists s. rewrite -> H.
  apply Val_eq_compat. rewrite -> H0. auto.
Qed.

Lemma Letty_unfold :
  forall (θ1 θ2 : type) (c : ctx)
    (t1 : term (θ1 :: c) θ1) (t2 : term (θ1 :: c) θ2)
    (ρ : ctx_denot c),
    ⟦ term_let c θ1 θ2 t1 t2 ⟧ ρ =-= ⟦ t2 ⟧ (FixF ⟦ t1 ⟧ ρ, ρ).
Proof.
  auto.
Qed.

Lemma prod_fun_prop : forall (A B C : cpoType) (d : A -=> B _BOT) (d' : A -=> C _BOT),
    cprod_fun d d' =-= eta << prod_fun d d'.
Proof.
  intros A B C d d'.
  split.
  intro a. by simpl.
  intro a. by simpl.
Qed.
