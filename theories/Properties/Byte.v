(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Bytes Properties *)

Lemma of_bits_to_bits (b : byte) : of_bits (to_bits b) = b.
Proof. destruct b; exact eq_refl. Qed.

Lemma to_bits_of_bits (b : _) : to_bits (of_bits b) = b.
Proof.
  repeat match goal with
         | p : prod _ _ |- _ => destruct p
         | b : bool |- _ => destruct b
         end;
    exact eq_refl.
Qed.
