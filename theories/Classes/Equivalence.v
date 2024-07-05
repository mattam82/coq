(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Typeclass-based setoids. Definitions on [Equivalence].

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.

Require Import Coq.Classes.Init.
Require Export Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables A R eqA B S eqB.
Local Obligation Tactic := try solve [simpl_relation].

Local Open Scope signature_scope.

Definition equiv@{s s' | u v|} `{Equivalence@{s s' | u v} A R} : relation A := R.

(** Overloaded notations for setoid equivalence and inequivalence.
    Not to be confused with [eq] and [=]. *)

Declare Scope equiv_scope.

Notation " x === y " := (equiv x y) (at level 70, no associativity) : equiv_scope.

Notation " x =/= y " := (complement equiv x y) (at level 70, no associativity) : equiv_scope.

Local Open Scope equiv_scope.

(** Overloading for [PER]. *)

Definition pequiv@{s s' | u v|} `{PER@{s s' | u v} A R} : relation A := R.

(** Overloaded notation for partial equivalence. *)

Infix "=~=" := pequiv (at level 70, no associativity) : equiv_scope.

(** Shortcuts to make proof search easier. *)

#[global]
Program Instance equiv_reflexive@{s s' | u v|} `(sa : Equivalence@{s s' | u v} A) : Reflexive equiv.

#[global]
Program Instance equiv_symmetric@{s s' | u v|} `(sa : Equivalence@{s s' | u v} A) : Symmetric equiv.

#[global]
Program Instance equiv_transitive@{s s' | u v|} `(sa : Equivalence@{s s' | u v} A) : Transitive equiv.
Next Obligation.
intros; eapply transitivity; eauto.
Qed.

Arguments equiv_symmetric {A R} sa x y : rename.
Arguments equiv_transitive {A R} sa x y z : rename.

(** Use the [substitute] command which substitutes an equivalence in every hypothesis. *)

Ltac setoid_subst H :=
  match type of H with
    ?x === ?y => substitute H ; clear H x
  end.

Ltac setoid_subst_nofail :=
  match goal with
    | [ H : ?x === ?y |- _ ] => setoid_subst H ; setoid_subst_nofail
    | _ => idtac
  end.

(** [subst*] will try its best at substituting every equality in the goal. *)

Tactic Notation "subst" "*" := subst_no_fail ; setoid_subst_nofail.

(** Simplify the goal w.r.t. equivalence. *)

Ltac equiv_simplify_one :=
  match goal with
    | [ H : ?x === ?x |- _ ] => clear H
    | [ H : ?x === ?y |- _ ] => setoid_subst H
    | [ |- ?x =/= ?y ] => let name:=fresh "Hneq" in intro name
    | [ |- ~ ?x === ?y ] => let name:=fresh "Hneq" in intro name
  end.

Ltac equiv_simplify := repeat equiv_simplify_one.

(** "reify" relations which are equivalences to applications of the overloaded [equiv] method
   for easy recognition in tactics. *)

Ltac equivify_tac :=
  match goal with
    | [ s : Equivalence ?A ?R, H : ?R ?x ?y |- _ ] => change R with (@equiv A R s) in H
    | [ s : Equivalence ?A ?R |- context C [ ?R ?x ?y ] ] => change (R x y) with (@equiv A R s x y)
  end.

Ltac equivify := repeat equivify_tac.

(*
Section Respecting.

  (** Here we build an equivalence instance for functions which relates respectful ones only,
     we do not export it. *)

  Sort s s' s''.
  Universe u v w x l.
  Definition respecting@{u v w x l|?}
      `(eqa : Equivalence@{s s''| u v} A (R : relation A),
        eqb : Equivalence@{s' s'|w x} B (R' : relation B)) : Type@{s'|l} :=
    { morph & respectful@{s s'' s' s'| u v w x l} R R' morph morph}.

  Program Instance respecting_equiv `(eqa : Equivalence A R, eqb : Equivalence B R') :
    Equivalence (fun (f g : respecting eqa eqb) =>
                   forall (x y : A), R x y -> R' (fst f x) (fst g y)).

  Solve Obligations with unfold respecting in * ; simpl_relation ; program_simpl.

  Next Obligation.
  Proof.
    red; intros. unfold respecting in *. program_simpl. reflexivity.
  Qed.

  Next Obligation.
  Proof.
  intros; eapply symmetry;eauto.
  Qed.

  Next Obligation.
  Proof.
    intros. intros f g h H H' x y Rxy.
    unfold respecting in *. program_simpl. transitivity (g y); auto. firstorder.
  Qed.

End Respecting.
*)

(** The default equivalence on function spaces, with higher-priority than [eq]. *)
Set Printing Universes.
#[global]
Instance pointwise_reflexive@{s s' s''|u v w|} {A : Type@{s | u}} `(reflb : Reflexive@{s' s'' | v w} B eqB) :
  Reflexive (pointwise_relation A eqB) | 9.
Proof. firstorder. Qed.
#[global]
Instance pointwise_symmetric@{s s' s'' | u v w|} {A : Type@{s | u}} `(symb : Symmetric@{s' s'' | v w} B eqB) :
  Symmetric (pointwise_relation A eqB) | 9.
Proof. firstorder. Qed.
#[global]
Instance pointwise_transitive@{s s' s'' | u v w|} {A : Type@{s | u}} `(transb : Transitive@{s' s'' | v w} B eqB) :
  Transitive (pointwise_relation A eqB) | 9.
Proof. firstorder. Qed.
#[global]
Instance pointwise_equivalence@{s s' s'' | u v w|} {A : Type@{s|u}} `(eqb : Equivalence@{s' s'' | v w} B eqB) :
  Equivalence (pointwise_relation A eqB) | 9.
Proof. split; apply _. Qed.
