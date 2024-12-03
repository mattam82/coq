(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Section Equivalence.
  Sort s.
  Universe u.

  Theorem iff_refl : forall A:Type@{s|u}, A <-> A.
    Proof.
      split; auto.
    Qed.
  Universe v.
  Theorem iff_sym : forall (A:Type@{s|u}) (B:Type@{s|v}), (A <-> B) -> (B <-> A).
    Proof.
      intros A B [H1 H2]; split; auto.
    Qed.

  Universe w.
  Theorem iff_trans : forall (A:Type@{s|u}) (B:Type@{s|v}) (C:Type@{s|w}), (A <-> B) -> (B <-> C) -> (A <-> C).
  Proof.
    intros A B C [H1 H2] [H3 H4]; split; auto.
  Qed.



End Equivalence.

#[global]
Hint Unfold iff: extcore.
