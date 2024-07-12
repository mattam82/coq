(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

Require Export Stdlib.Classes.Init.
Require Import Stdlib.Program.Basics.
Require Import Stdlib.Program.Tactics.

Require Import Stdlib.Properties.GroupoidLaws.
Require Export Stdlib.Properties.Functions.

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
  Lemma complement_inverse R : complement (flip R) = flip (complement R).
  Proof. reflexivity. Qed.

  Class Irreflexive (R : relation A) :=
    irreflexivity : Reflexive (complement R).

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
    #[global] PreOrder_Reflexive :: Reflexive R | 2 ;
    #[global] PreOrder_Transitive :: Transitive R | 2 }.

  (** A [StrictOrder] is both Irreflexive and Transitive. *)

  #[projections(primitive=no)]
  Class StrictOrder (R : relation A)  := {
    #[global] StrictOrder_Irreflexive :: Irreflexive R ;
    #[global] StrictOrder_Transitive :: Transitive R }.

  (** By definition, a strict order is also asymmetric *)
  Global Instance StrictOrder_Asymmetric `(StrictOrder R) : Asymmetric R.
  Proof. firstorder. Qed.

  (** A partial equivalence relation is Symmetric and Transitive. *)

  #[projections(primitive=no)]
  Class PER (R : relation A)  := {
    #[global] PER_Symmetric :: Symmetric R | 3 ;
    #[global] PER_Transitive :: Transitive R | 3 }.

  (** Equivalence relations. *)

  #[projections(primitive=no)]
  Class Equivalence (R : relation A)  := {
    #[global] Equivalence_Reflexive :: Reflexive R ;
    #[global] Equivalence_Symmetric :: Symmetric R ;
    #[global] Equivalence_Transitive :: Transitive R }.

  (** An Equivalence is a PER plus reflexivity. *)

  Global Instance Equivalence_PER {R} `(Equivalence R) : PER R | 10 :=
    { PER_Symmetric := Equivalence_Symmetric ;
      PER_Transitive := Equivalence_Transitive }.

  (** We can now define antisymmetry w.r.t. an equivalence relation on the carrier. *)

  Class Antisymmetric eqA `{equ : Equivalence eqA} (R : relation A) :=
    antisymmetry : forall {x y}, R x y -> R y x -> eqA x y.

  Class subrelation (R: relation A) (R' : relation A) :=
    is_subrelation : forall {x y}, R x y -> R' x y.

  (** Any symmetric relation is equal to its inverse. *)

  Lemma subrelation_symmetric R `(Symmetric R) : subrelation (flip R) R.
  Proof. hnf. intros x y H'. red in H'. apply symmetry. assumption. Qed.

  Section flip.

    Lemma flip_Reflexive `{Reflexive R} : Reflexive (flip R).
    Proof. tauto. Qed.

    Program Definition flip_Irreflexive `(Irreflexive R) : Irreflexive (flip R) :=
      irreflexivity (R:=R).

    Program Definition flip_Symmetric `(Symmetric R) : Symmetric (flip R) :=
      fun x y H => symmetry (R:=R) H.

    Program Definition flip_Asymmetric `(Asymmetric R) : Asymmetric (flip R) :=
      fun x y H H' => asymmetry (R:=R) H H'.

    Program Definition flip_Transitive `(Transitive R) : Transitive (flip R) :=
      fun x y z H H' => transitivity (R:=R) _ H' H.

    Program Definition flip_Antisymmetric `(Antisymmetric eqA R) :
      Antisymmetric eqA (flip R).
    Proof. firstorder. Qed.

    (** Inversing the larger structures *)

    Lemma flip_PreOrder `(PreOrder R) : PreOrder (flip R).
    Proof. firstorder. Qed.

    Lemma flip_StrictOrder `(StrictOrder R) : StrictOrder (flip R).
    Proof. firstorder. Qed.

    Lemma flip_PER `(PER R) : PER (flip R).
    Proof. firstorder. Qed.

    Lemma flip_Equivalence `(Equivalence R) : Equivalence (flip R).
    Proof. firstorder. Qed.

  End flip.

  Section complement.

    Definition complement_Irreflexive `(Reflexive R)
      : Irreflexive (complement R).
    Proof. firstorder. Qed.

    Definition complement_Symmetric `(Symmetric R) : Symmetric (complement R).
    Proof. firstorder. Qed.
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

  Global Instance equivalence_rewrite_relation `(Equivalence eqA) : RewriteRelation eqA.
  Defined.

  (** Leibniz equality. *)
  Section Leibniz.
    Global Instance eq_Reflexive : Reflexive (@eq A) := @eq_refl A.
    Global Instance eq_Symmetric : Symmetric (@eq A) := @eq_sym A.
    Global Instance eq_Transitive : Transitive (@eq A) := @eq_trans A.

    (** Leibinz equality [eq] is an equivalence relation.
        The instance has low priority as it is always applicable
        if only the type is constrained. *)

    Global Program Instance eq_equivalence : Equivalence (@eq A) | 10.
  End Leibniz.

End Defs.

Global Arguments transitivity {A R Transitive x} y {z}.

(** Default rewrite relations handled by [setoid_rewrite]. *)
#[global]
Instance rr_impl@{s|u|} : RewriteRelation arrow@{s s|u u}.
Defined.


#[global]
Instance rr_iff@{s|u|} : RewriteRelation iff@{s|u u}.
Defined.

(** Hints to drive the typeclass resolution avoiding loops
 due to the use of full unification. *)
#[global]
Hint Extern 1 (Reflexive (complement _)) => class_apply @irreflexivity : typeclass_instances.
#[global]
Hint Extern 3 (Symmetric (complement _)) => class_apply complement_Symmetric : typeclass_instances.
#[global]
Hint Extern 3 (Irreflexive (complement _)) => class_apply complement_Irreflexive : typeclass_instances.

#[global]
Hint Extern 3 (Reflexive (flip _)) => apply flip_Reflexive : typeclass_instances.
#[global]
Hint Extern 3 (Irreflexive (flip _)) => class_apply flip_Irreflexive : typeclass_instances.
#[global]
Hint Extern 3 (Symmetric (flip _)) => class_apply flip_Symmetric : typeclass_instances.
#[global]
Hint Extern 3 (Asymmetric (flip _)) => class_apply flip_Asymmetric : typeclass_instances.
#[global]
Hint Extern 3 (Antisymmetric (flip _)) => class_apply flip_Antisymmetric : typeclass_instances.
#[global]
Hint Extern 3 (Transitive (flip _)) => class_apply flip_Transitive : typeclass_instances.
#[global]
Hint Extern 3 (StrictOrder (flip _)) => class_apply flip_StrictOrder : typeclass_instances.
#[global]
Hint Extern 3 (PreOrder (flip _)) => class_apply flip_PreOrder : typeclass_instances.

#[global]
Hint Extern 4 (subrelation (flip _) _) =>
  class_apply @subrelation_symmetric : typeclass_instances.

#[global]
Hint Resolve irreflexivity : ord.

Unset Implicit Arguments.

Ltac solve_relation :=
  match goal with
  | [ |- ?R ?x ?x ] => reflexivity
  | [ H : ?R ?x ?y |- ?R ?y ?x ] => symmetry ; exact H
  end.

#[global]
Hint Extern 4 => solve_relation : relations.

(** We can already dualize all these properties. *)

(** * Standard instances. *)

Ltac reduce_hyp H :=
  match type of H with
    | context [ _ <-> _ ] => fail 1
    | _ => red in H ; try reduce_hyp H
  end.

Ltac reduce_goal :=
  match goal with
    | [ |- _ <-> _ ] => fail 1
    | _ => red ; intros ; try reduce_goal
  end.

Tactic Notation "reduce" "in" hyp(Hid) := reduce_hyp Hid.

Ltac reduce := reduce_goal.

Tactic Notation "apply" "*" constr(t) :=
  first [ refine t | refine (t _) | refine (t _ _) | refine (t _ _ _) | refine (t _ _ _ _) |
    refine (t _ _ _ _ _) | refine (t _ _ _ _ _ _) | refine (t _ _ _ _ _ _ _) ].

Ltac simpl_relation :=
  unfold flip, arrow ; try reduce ; program_simpl ;
    try ( solve [ dintuition auto with relations ]).

Local Obligation Tactic := simpl_relation.

(** Logical implication. *)

#[global]
Program Instance impl_Reflexive@{s|u|} : Reflexive arrow@{s s|u u}.
#[global]
Program Instance impl_Transitive@{s|u|} : Transitive arrow@{s s|u u}.

(** Logical equivalence. *)

#[global]
Instance iff_Reflexive@{s|u|} : Reflexive iff@{s|u u} := iff_refl.
#[global]
Instance iff_Symmetric@{s|u|} : Symmetric iff@{s|u u} := iff_sym.
#[global]
Instance iff_Transitive@{s|u|} : Transitive iff@{s|u u} := iff_trans.

(** Logical equivalence [iff] is an equivalence relation. *)

#[global]
Program Instance iff_equivalence@{s|u|} : Equivalence iff@{s|u u}.
#[global]
Program Instance arrow_Reflexive@{s|u|} : Reflexive arrow@{s s|u u}.
#[global]
Program Instance arrow_Transitive@{s|u|} : Transitive arrow@{s s|u u}.

(** We now develop a generalization of results on relations for arbitrary predicates.
   The resulting theory can be applied to homogeneous binary relations but also to
   arbitrary n-ary predicates. *)

Local Open Scope list_scope.

(** A compact representation of non-dependent arities, with the codomain singled-out. *)

(** We define the various operations which define the algebra on binary relations *)
Section Binary.
  Sort s s'.
  Universe u v.
  Context {A : Type@{s|u}}.

  Definition relation_equivalence : relation@{Type s'|_ _} (relation@{s s'|u v} A)
    := fun R R' => forall x y, iff (R x y) (R' x y).

  Global Instance: RewriteRelation relation_equivalence.
  Defined.

  Definition relation_conjunction (R : relation@{s s'|u v} A) (R' : relation@{s s'|u v} A) : relation A :=
    fun x y => prod (R x y) (R' x y).

  Definition relation_disjunction (R : relation@{s s'|u v} A) (R' : relation@{s s'|u v} A) : relation A :=

    fun x y => sum (R x y) (R' x y).
  (** Relation equivalence is an equivalence, and subrelation defines a partial order. *)

  Global Instance relation_equivalence_equivalence :
    Equivalence relation_equivalence.
  Proof.
    split; red; unfold relation_equivalence, iff.
    - intros **. split; intros ?; assumption.
    - intros **. edestruct X. split; eassumption.
    - intros x y z X X0 x0 y0. destruct (X x0 y0). destruct (X0 x0 y0). split; eauto.
  Qed.

  Global Instance relation_implication_preorder : PreOrder (@subrelation A).
  Proof. firstorder. Qed.

  (** *** Partial Order.
   A partial order is a preorder which is additionally antisymmetric.
   We give an equivalent definition, up-to an equivalence relation
   on the carrier. *)

  Class PartialOrder eqA `{equ : Equivalence A eqA} R `{preo : PreOrder A R} :=
    partial_order_equivalence : relation_equivalence eqA (relation_conjunction R (flip R)).

  (** The equivalence proof is sufficient for proving that [R] must be a
   morphism for equivalence (see Morphisms).  It is also sufficient to
   show that [R] is antisymmetric w.r.t. [eqA] *)

  Global Instance partial_order_antisym `(PartialOrder eqA R) : Antisymmetric eqA R.
  Proof with auto.
    reduce_goal.
    firstorder.
  Qed.

  Lemma PartialOrder_inverse `(PartialOrder eqA R) : PartialOrder eqA (flip R).
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

#[global]
Hint Extern 3 (PartialOrder (flip _)) => class_apply PartialOrder_inverse : typeclass_instances.

(** The partial order defined by subrelation and relation equivalence. *)

(* Program Instance subrelation_partial_order : *)
(*   ! PartialOrder (relation A) relation_equivalence subrelation. *)
(* Obligation Tactic := idtac. *)

(* Next Obligation. *)
(* Proof. *)
(*   intros x. refine (fun x => x). *)
(* Qed. *)

Global Typeclasses Opaque relation_equivalence.

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
