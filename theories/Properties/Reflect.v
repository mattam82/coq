(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Properties of the reflect predicate *)
Goal forall b (r : reflect True b), b = true.
Proof.
  intros b r. destruct r; try reflexivity.
  contradiction.
Qed.

(** Relation with iff : *)

Lemma reflect_iff : forall P b, reflect P b -> (P<->b=true).
Proof.
 destruct 1; intuition; discriminate.
Qed.

Lemma iff_reflect : forall P b, (P<->b=true) -> reflect P b.
Proof.
 destruct b; econstructor; intuition. discriminate H.
Defined.

(** It would be nice to join [reflect_iff] and [iff_reflect]
    in a unique [iff] statement, but this isn't allowed since
    [iff] is in Prop. *)

(** Reflect implies decidability of the proposition *)

Lemma reflect_dec : forall P b, reflect P b -> {P}+{~P}.
Proof.
 destruct 1; auto.
Defined.
