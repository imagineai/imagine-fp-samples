Add Rec LoadPath "." as Top.

Set Automatic Coercions Import.
Set Implicit Arguments.

Require Import Utf8.
Require Import Machine.
Require Import Ensembles.
Require Import Equalities.

Add LoadPath "../denot".
Add LoadPath "../denot/domain-theory".
Require Import Sets.
Require Import StepIndexing.

(** * Set of observations (configurations) *)

Module Type ObservationsSI (PointerType : UsualDecidableType).

  Module Export M := Machine PointerType.

  Definition SetIn := Ensembles.In.

  Definition ConfSet := iSet conf.
  Parameter Ω : ConfSet.

  (** The set is closed by anti-execution *) 
  Parameter antiex : forall w w' (i : nat), w ↦ w' ->
                                     SetIn (Ω i) w' ->
                                     SetIn (Ω (S i)) w.

  Parameter stepI : StepI Ω.

  (** Extending the heap with unreachable pointers is safe. Unreachability
      ensured by asking for well-formedness of the configuration *)
  Parameter extend_heap:
    forall i Γ Δ α s, Γ ⋈ Δ -> conf_wf (Γ, α, s) ->
                 SetIn (Ω i) (Γ, α, s) ->
                 SetIn (Ω i) (Γ ∪ Δ, α, s).

  (** Order an update of the heap is safe *)
  Parameter add_marker:
    forall i Γ α β s p,
      find p Γ = Some β ->
      HClos_to_MClos β = Some α ->
      SetIn (Ω i) (Γ, α, s) -> SetIn (Ω i) (Γ, α, # p :: s).

  Parameter add_marker_pi1:
    forall i Γ α β s p,
      find p Γ = Some β ->
      HClos_to_MClos β = Some α ->
      SetIn (Ω i) (Γ, α, mapplypi1 :: s) ->
      SetIn (Ω i) (Γ, α, # p ::  mapplypi1 :: #1 p :: s).
  
  Parameter add_marker_pi2:
    forall i Γ α β s p,
      find p Γ = Some β ->
      HClos_to_MClos β = Some α ->
      SetIn (Ω i) (Γ, α, mapplypi2 :: s) ->
      SetIn (Ω i) (Γ, α, # p ::  mapplypi2 :: #2 p :: s).
  
  (** The set is closed under a notion of equality under configurations *)
  (** Almost leibniz in this case, except for the heap for which we use
      [FMapInterface.Equal] **)
  Parameter eq_closed:
    forall w w' i, w [==] w' -> SetIn (Ω i) w -> SetIn (Ω i) w'.
  
End ObservationsSI.


(** TODO: Prove this properties for a concrete set. 
The set of configurations that terminate satisfy those rules, but I didn't
formalize the proofs (because it is a ton of work) *)

(* Local Variables: *)
(* company-coq-local-symbols: (("~>" . ?↣)) *)
(* End: *)
