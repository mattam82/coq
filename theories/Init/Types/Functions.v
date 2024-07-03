(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import PreludeOptions.
Require Import Notations.
Require Import Sigma.

Definition id@{s|u|} {A : Type@{s|u}} (a : A) := a.

Definition arrow@{s s'|u v|} (A : Type@{s|u}) (B : Type@{s'|v}) := A -> B.
Register arrow as core.arrow.
Register arrow as core.impl.

Notation impl := arrow.

Definition compose@{s s' s''|u v w|}
  {A : Type@{s|u}} {B : Type@{s'|v}} {C : Type@{s''|w}}
  (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Definition flip@{s s' s''|u v w|} {A : Type@{s|u}} {B : Type@{s'|v}} {C : Type@{s''|w}}
  (f : A -> B -> C) := fun x y => f y x.
Register flip as core.flip.

Definition apply@{s s'|u v|} {A : Type@{s|u}} {B : Type@{s'|v}} (f : A -> B) (x : A) := f x.

Definition iff@{s|u v|} (A : Type@{s|u}) (B : Type@{s|v}) := (A -> B) * (B -> A).
Register iff as core.iff.type.
Register fst as core.iff.proj1.
Register snd as core.iff.proj2.

Definition const@{s s'|u v|} {A : Type@{s|u}} {B : Type@{s'|v}} (a : A) := fun _ : B => a.

Definition all@{s s'|u v|} (A:Type@{s|u}) (P:A -> Type@{s'|v}) := forall x:A, P x.
Register all as core.all.

Notation "x <-> y" := (iff x y).
