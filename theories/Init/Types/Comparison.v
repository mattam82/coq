(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Corelib Require Import Init.Types.Unit.

(********************************************************************)
(** * The comparison datatype *)

Inductive comparison : Set :=
  | Eq : comparison
  | Lt : comparison
  | Gt : comparison.

Register comparison as core.comparison.type.
Register Eq as core.comparison.Eq.
Register Lt as core.comparison.Lt.
Register Gt as core.comparison.Gt.

Definition CompOpp (r:comparison) :=
  match r with
    | Eq => Eq
    | Lt => Gt
    | Gt => Lt
  end.

(*Lemma CompOpp_involutive c : CompOpp (CompOpp c) = c.
Proof.
  destruct c; reflexivity.
Qed.

Lemma CompOpp_inj c c' : CompOpp c = CompOpp c' -> c = c'.
Proof.
  destruct c; destruct c'; auto; discriminate.
Qed.

Lemma CompOpp_iff : forall c c', CompOpp c = c' <-> c = CompOpp c'.
Proof.
  split; intros; apply CompOpp_inj; rewrite CompOpp_involutive; auto.
Qed. *)
