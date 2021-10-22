(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Testing universe expresion handling. *)

Set Universe Polymorphism.

Definition crelation (A : Type) := A -> A -> Type.

Definition arrow (A B : Type) := A -> B.

Definition flip {A B C : Type} (f : A -> B -> C) := fun x y => f y x.

Definition iffT (A B : Type) := ((A -> B) * (B -> A))%type.

(** We allow to unfold the [crelation] definition while doing morphism search. *)

Section algebra.
  Universes u v w.
  Constraint u < v.
  Constraint u+1 = v.
  Fail Constraint v = u.
  Fail Constraint v = u+2.
  Constraint v = u+1.
End algebra.

Axiom strorder@{u u0} : forall {A : Type@{u}} (_ : crelation@{u u0} A), Type@{max(u,u0)}.

Section bugplus.
  Universe u.
  Context {A : Type@{u}}.
  Universe v.
  Context {R : crelation@{u v+1} A}.
  Set Debug "universes".
  Lemma foo@{u1 u2} : True.
  Proof.
    set (t := strorder@{u1 u2} R).
    Show Universes.
    red in R.





Section Defs.
  Universe u.
  Context {A : Type@{u}}.

  (** We rebind crelational properties in separate classes to be able to overload each proof. *)

  Class Reflexive (R : crelation A) :=
    reflexivity : forall x : A, R x x.

  Definition complement@{ur} (R : crelation@{u ur} A) : crelation@{u ur} A :=
    fun x y => R x y -> False.

  (** These are convertible. *)
  Lemma complement_inverse (R : crelation A) : complement (flip R) = flip (complement R).
  Proof. reflexivity. Qed.

  Goal True.
    pose proof complement_inverse.
  Set Printing Universes.
  About complement_inverse.
