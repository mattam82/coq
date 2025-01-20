(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Corelib Require Import PreludeOptions.
From Corelib Require Import Notations.
From Corelib Require Import Types.Bool.
From Corelib Require Import Types.Empty.

(************************************************)
(** * Reflect: a specialized inductive type for
    relating propositions and booleans
************************************************)

Inductive reflect@{s sb se|l|} (P : 𝒰@{s|l}) : bool@{sb|} -> Type@{se |l} :=
 | ReflectT : P -> reflect P true
 | ReflectF : ~ P -> reflect P false.

#[global]
Hint Constructors reflect : bool.
Arguments ReflectT : clear implicits.
Arguments ReflectF : clear implicits.
