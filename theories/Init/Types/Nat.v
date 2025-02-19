(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import PreludeOptions.
Require Import Notations.

Declare Scope nat_scope.

Section NatSortPoly.
  Sort s.

  Inductive nat : Type@{s|0} :=
    | O : nat
    | S (_ : nat) : nat.

  Fixpoint plus (a b : nat) : nat :=
    match a with
      | O => b
      | S n => S (n + b)
    end
  where "n + m" := (plus n m) : nat_scope.

  Definition pred (a : nat) : nat :=
    match a with
      | O => O
      | S n => n
    end.

End NatSortPoly.

Notation "n + m" := (plus n m) : nat_scope.
Declare Scope hex_nat_scope.
Delimit Scope hex_nat_scope with xnat.
Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.

Arguments S _%_nat.

Definition nat_rect@{s | u|} : forall P : nat@{Type|} -> Type@{s | u},
  P O -> (forall n : nat@{Type|}, P n -> P (S n)) -> forall n : nat@{Type|}, P n :=
  fun P f f0 =>
  fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | O => f
  | S n0 => f0 n0 (F n0)
  end.

Definition nat_ind := nat_rect@{Prop|0}.

Register nat as num.nat.type.
Register O as num.nat.O.
Register S as num.nat.S.

Local Open Scope nat_scope.
