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
Require Import Empty.

Inductive eq@{s s'|l|} {A:Type@{s|l}} (x:A) : A -> Type@{s'|l} :=
    eq_refl : eq x x.

Notation "x = y :> A" := (@eq A x y) : type_scope.

Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.

Scheme eq_poly := Induction for eq Sort Poly.

Definition eq_ind@{s | u|} [A] [x] P := @eq_poly@{s Prop|u Set} A x (fun a _ => P a).

Definition eq_singleton@{s s' | u v|} [A:Type@{s|u}] [x:A]
  (P : forall a : A, (eq@{s Prop|u} x a) -> Type@{s'|v}) :
  P x (eq_refl x) -> forall [a : A] (e : x = a :> A), P a e :=
  fun t _ e => match e with eq_refl => t end.

Definition eq_rect@{u v|} [A:Type@{u}] [x:A]
  (P : forall a : A, Type@{v}) :
  P x -> forall [a : A] (e : x = a :> A), P a := @eq_singleton A x (fun a _ => P a).

Definition eq_rec@{u|} [A:Type@{u}] [x:A]
  (P : forall a : A, Set) :
  P x -> forall [a : A] (e : x = a :> A), P a := @eq_singleton@{_ _| _ Set} A x (fun a _ => P a).

Definition eq_sind [A:Set] [x:A]
  (P : forall a : A, SProp) :
  P x -> forall [a : A] (e : x = a :> A), P a := @eq_singleton A x (fun a _ => P a).

Arguments eq_ind [A] x P _ y _ : rename.
Arguments eq_sind [A] x P _ y _ : rename.
Arguments eq_rec [A] x P _ y _ : rename.
Arguments eq_rect [A] x P _ y _ : rename.

Notation "x = y" := (eq@{_ Prop|_} x y) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (~ (x = y)) : type_scope.

#[global]
Hint Resolve eq_refl: core.

Register eq as core.eq.type.
Register eq_refl as core.eq.refl.
Register eq_ind as core.eq.ind.
Register eq_rect as core.eq.rect.
Register eq_poly as core.eq.rect.
