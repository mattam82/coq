(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Decimal number properties *)

From Corelib.Init.Types Require Import Decimal Hexadecimal Sum.
From Corelib.Properties Require Import Bool.
From Corelib Require Import Init.Types.Unit.

Scheme Equality for uint.
Scheme Equality for int.
Scheme Equality for hexadecimal.
Notation int_eq_dec := signed_int_eq_dec.
Notation int_beq := signed_int_beq.
Notation internal_int_dec_lb := internal_signed_int_dec_lb.
Notation internal_int_dec_bl := internal_signed_int_dec_bl.
