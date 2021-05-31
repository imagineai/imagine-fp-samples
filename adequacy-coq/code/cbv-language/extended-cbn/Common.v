(** * Common: Shared definitions *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Import Setoid.
Require Export Arith.
Require Import List.
Require Import NaryFunctions.

(** We use De Bruijn indices to represent binders *)
Definition var := nat.

(** Finite products of nats *)
Fixpoint natn n : Type := nprod nat n.