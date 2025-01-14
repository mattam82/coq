(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Definition sumbool_of_bool (b : bool) : {b = true} + {b = false} :=
  if b return {b = true} + {b = false} then left eq_refl else right eq_refl.

Hint Resolve sumbool_of_bool : bool.
