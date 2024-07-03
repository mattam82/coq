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

Definition flip@{s s' s''|u v w|} {A : Type@{s|u}} {B : Type@{s'|v}} {C : Type@{s''|w}}
  (f : A -> B -> C) := fun x y => f y x.

Definition iff@{s|u v|} (A : Type@{s|u}) (B : Type@{s|v}) := (A -> B) * (B -> A).
