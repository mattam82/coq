(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Typeclass-based relations, tactics and standard instances

   This is the basic theory needed to formalize morphisms and setoids.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

(*
Require Import Corelib.Program.Basics.
Require Import Corelib.Program.Tactics.
*)

Require Export Corelib.Init.PreludeOptions.
Require Export Corelib.Init.Notations.
Require Export Corelib.Init.Classes.
Require Export Corelib.Init.Types.Functions.
Require Export Corelib.Init.Types.Equality.
Require Export Corelib.Init.Types.Sigma.
Require Export Corelib.Init.Types.Sum.
Require Export Corelib.Init.Types.Empty.
Require Export Corelib.Init.Tactics.Ltac.

Generalizable Variables A B C D R S T U l eqA eqB eqC eqD.

(** We allow to unfold the [relation] definition while doing morphism search. *)

(** listings: relation **)
Section Defs.
  Sort s s'. Universe u v.
  Definition relation (A : Type@{s|u}) := A -> A -> Type@{s'|v}.
  Context {A : Type@{s|u}}.
  Class Reflexive (R : relation A) := reflexivity : forall x : A, R x x.
(** listings: end **)

  Definition complement (R : relation A) : relation A :=
    fun x y => R x y -> empty.

  (** Opaque for proof-search. *)
  Typeclasses Opaque complement iff.

  (** These are convertible. *)
(*
  Lemma complement_inverse R : complement (flip R) = flip (complement R).
  Proof. reflexivity. Qed.
*)
  Class Irreflexive (R : relation A) :=
    irreflexivity : Reflexive (complement R).

  Arguments irreflexivity _ {_} _.

  Class Symmetric (R : relation A) :=
    symmetry : forall {x y}, R x y -> R y x.

  Class Asymmetric (R : relation A) :=
    asymmetry : forall {x y}, R x y -> (complement R y x : Type@{s'|v}).

  Class Transitive (R : relation A) :=
    transitivity : forall {x y z}, R x y -> R y z -> R x z.

  Arguments transitivity {R Transitive x} y {z}.

  (** Various combinations of reflexivity, symmetry and transitivity. *)

  (** A [PreOrder] is both Reflexive and Transitive. *)

  #[projections(primitive=no)]
  Class PreOrder (R : relation A)  := {
    #[export] PreOrder_Reflexive :: Reflexive R | 2 ;
    #[export] PreOrder_Transitive :: Transitive R | 2 }.

  (** A [StrictOrder] is both Irreflexive and Transitive. *)

  #[projections(primitive=no)]
  Class StrictOrder (R : relation A)  := {
    #[export] StrictOrder_Irreflexive :: Irreflexive R ;
    #[export] StrictOrder_Transitive :: Transitive R }.

  (** By definition, a strict order is also asymmetric *)
  #[export]
  Instance StrictOrder_Asymmetric `(StrictOrder R) : Asymmetric R.
  Proof. intros x y e X. eapply (irreflexivity R x). apply (transitivity y); eauto. Defined.

  (** A partial equivalence relation is Symmetric and Transitive. *)

  #[projections(primitive=no)]
  Class PER (R : relation A)  := {
    #[export] PER_Symmetric :: Symmetric R | 3 ;
    #[export] PER_Transitive :: Transitive R | 3 }.

  (** Equivalence relations. *)

  #[projections(primitive=no)]
  Class Equivalence (R : relation A)  := {
    #[export] Equivalence_Reflexive :: Reflexive R ;
    #[export] Equivalence_Symmetric :: Symmetric R ;
    #[export] Equivalence_Transitive :: Transitive R }.

  (** An Equivalence is a PER plus reflexivity. *)

  #[export]
  Instance Equivalence_PER {R} `(Equivalence R) : PER R | 10 :=
    { PER_Symmetric := Equivalence_Symmetric ;
      PER_Transitive := Equivalence_Transitive }.

  (** We can now define antisymmetry w.r.t. an equivalence relation on the carrier. *)

  Class Antisymmetric eqA `{equ : Equivalence eqA} (R : relation A) :=
    antisymmetry : forall {x y}, R x y -> R y x -> eqA x y.

  Arguments antisymmetry {_ _} _ {_ _ _} _ _.

  Class subrelation (R: relation A) (R' : relation A) :=
    is_subrelation : forall {x y}, R x y -> R' x y.

  (** Any symmetric relation is equal to its inverse. *)
  #[export]
  Instance subrelation_symmetric R `(Symmetric R) : subrelation (flip R) R.
  Proof. hnf. intros x y H'. red in H'. apply symmetry. assumption. Defined.

  Section flip.

    #[export]
    Instance flip_Reflexive `{Reflexive R} : Reflexive (flip R).
    Proof. apply H. Defined.

    #[export]
    Instance flip_Irreflexive `(Irreflexive R) : Irreflexive (flip R) :=
      irreflexivity R.

    #[export]
    Instance flip_Symmetric `(Symmetric R) : Symmetric (flip R) :=
      fun x y H => symmetry (R:=R) H.

    #[export]
    Instance flip_Asymmetric `(Asymmetric R) : Asymmetric (flip R) :=
      fun x y H H' => asymmetry (R:=R) H H'.

    #[export]
    Instance flip_Transitive `(Transitive R) : Transitive (flip R) :=
      fun x y z H H' => transitivity (R:=R) _ H' H.

    #[export]
    Instance flip_Antisymmetric `(Antisymmetric eqA R) :
      Antisymmetric eqA (flip R).
    Proof. intros x y e e'. unfold flip in *. apply (antisymmetry R); eauto. Defined.

    (** Inversing the larger structures *)

    #[export]
    Instance flip_PreOrder `(PreOrder R) : PreOrder (flip R) := {}.
    #[export]
    Instance flip_StrictOrder `(StrictOrder R) : StrictOrder (flip R) := {}.
    #[export]
    Instance flip_PER `(PER R) : PER (flip R) := {}.
    #[export]
    Instance flip_Equivalence `(Equivalence R) : Equivalence (flip R) := {}.

  End flip.

  Section complement.

    #[export]
    Instance complement_Irreflexive `(Reflexive R): Irreflexive (complement R).
    Proof. intros x f. apply f; eauto. Defined.

    #[export]
    Instance complement_Symmetric `(Symmetric R) : Symmetric (complement R).
    Proof. unfold complement. intros x y f e . apply f. apply symmetry; auto. Defined.
  End complement.


  (** Rewrite relation on a given support: declares a relation as a rewrite
   relation for use by the generalized rewriting tactic.
   It helps choosing if a rewrite should be handled
   by the generalized or the regular rewriting tactic using leibniz equality.
   Users can declare an [RewriteRelation A RA] anywhere to declare default
   relations. This is also done automatically by the [Declare Relation A RA]
   commands. *)

  #[projections(primitive=no)]
  Class RewriteRelation (RA : relation A).

  (** Any [Equivalence] declared in the context is automatically considered
   a rewrite relation. *)

  Instance equivalence_rewrite_relation `(Equivalence eqA) : RewriteRelation eqA := {}.

End Defs.

Arguments irreflexivity {_} _ {_} _.
Arguments antisymmetry {_ _ _} _ {_ _ _} _ _.
Arguments transitivity {A R Transitive x} y {z}.

(** Default rewrite relations handled by [setoid_rewrite]. *)
#[export]
Instance rr_impl@{s|u|} : RewriteRelation arrow@{s s|u u} := {}.

#[export]
Instance rr_iff@{s|u|} : RewriteRelation iff@{s|u u}.
Defined.

#[export]
Hint Extern 4 (subrelation (flip _) _) =>
  class_apply @subrelation_symmetric : typeclass_instances.

(** We can already dualize all these properties. *)

(** * Standard instances. *)

(** Logical implication. *)

#[export]
Instance impl_Reflexive@{s|u|} : Reflexive arrow@{s s|u u} := fun A a => a.
#[export]
Instance impl_Transitive@{s|u|} : Transitive arrow@{s s|u u} := fun A B C f g x => g (f x).

(** We now develop a generalization of results on relations for arbitrary predicates.
   The resulting theory can be applied to homogeneous binary relations but also to
   arbitrary n-ary predicates. *)

(** A compact representation of non-dependent arities, with the codomain singled-out. *)

(** We define the various operations which define the algebra on binary relations *)
Section Binary.
  Sort s s'.
  Universe u v.
  Context {A : Type@{s|u}}.

  Definition relation_equivalence : relation@{Erased s'|_ _} (relation@{s s'|u v} A)
    := fun R R' => forall x y, iff (R x y) (R' x y).

  #[export]
  Instance: RewriteRelation relation_equivalence.
  Defined.

  Definition relation_conjunction (R : relation@{s s'|u v} A) (R' : relation@{s s'|u v} A) : relation A :=
    fun x y => prod (R x y) (R' x y).

  Definition relation_disjunction (R : relation@{s s'|u v} A) (R' : relation@{s s'|u v} A) : relation A :=

    fun x y => sum (R x y) (R' x y).
  (** Relation equivalence is an equivalence, and subrelation defines a partial order. *)

  #[export]
  Instance relation_equivalence_equivalence :
    Equivalence relation_equivalence.
  Proof.
    split; red; unfold relation_equivalence, iff.
    - intros **. split; intros ?; assumption.
    - intros **. edestruct X. split; eassumption.
    - intros x y z X X0 x0 y0. destruct (X x0 y0). destruct (X0 x0 y0). split; eauto.
  Defined.

  #[export]
  Instance relation_implication_preorder : PreOrder (@subrelation A).
  Proof. split; unfold subrelation; red; eauto. Defined.

  (** *** Partial Order.
   A partial order is a preorder which is additionally antisymmetric.
   We give an equivalent definition, up-to an equivalence relation
   on the carrier. *)

  Class PartialOrder@{w} (eqA : relation@{s s'|u v} A) `{equ : Equivalence A eqA} (R : relation@{s s'|u w} A) `{preo : PreOrder A R} :=
    partial_order_equivalence : relation_equivalence eqA (relation_conjunction R (flip R)).

  Arguments partial_order_equivalence {_ _} _ {_ _} _ _.

  (** The equivalence proof is sufficient for proving that [R] must be a
   morphism for equivalence (see Morphisms).  It is also sufficient to
   show that [R] is antisymmetric w.r.t. [eqA] *)

  #[export]
  Instance partial_order_antisym `(PartialOrder eqA R) : Antisymmetric eqA R.
  Proof with auto.
    red. intros x y r r'. apply (snd (partial_order_equivalence R x y)). split; eauto.
  Defined.

  #[export]
  Instance PartialOrder_inverse `(PartialOrder eqA R) : PartialOrder eqA (flip R).
  Proof.
    split.
    - intros X.
      specialize (H x y).
      destruct H as [H1 H2].
      specialize (H1 X).
      destruct H1.
      split; eauto.
    - intros X.
      specialize (H x y).
      destruct H as [H1 H2].
      eapply H2.
      destruct X. split; eauto.
  Qed.
End Binary.

Typeclasses Opaque relation_equivalence.

(* Register bindings for the generalized rewriting tactic *)

Register arrow as rewrite.type.arrow.
Register flip as rewrite.type.flip.
Register relation as rewrite.type.relation.
Register subrelation as rewrite.type.subrelation.
Register Reflexive as rewrite.type.Reflexive.
Register reflexivity as rewrite.type.reflexivity.
Register Symmetric as rewrite.type.Symmetric.
Register symmetry as rewrite.type.symmetry.
Register Transitive as rewrite.type.Transitive.
Register transitivity as rewrite.type.transitivity.
Register RewriteRelation as rewrite.type.RewriteRelation.
