(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** List Properties *)

Section Compare.

  Variable A : Type.
  Variable cmp : A -> A -> comparison.

  Fixpoint list_compare (xs ys : list A) : comparison :=
    match xs, ys with
    | nil   , nil    => Eq
    | nil   , _      => Lt
    | _     , nil    => Gt
    | x :: xs, y :: ys =>
        match cmp x y with
        | Eq => list_compare xs ys
        | c  => c
        end
    end%list.

End Compare.

Arguments list_compare [_] _ _ _.
