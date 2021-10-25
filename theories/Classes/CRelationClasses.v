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

Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.

Generalizable Variables A B C D R S T U l eqA eqB eqC eqD.

Set Universe Polymorphism.

Definition crelation (A : Type) := A -> A -> Type.

Definition arrow (A B : Type) := A -> B.

Definition flip {A B C : Type} (f : A -> B -> C) := fun x y => f y x.

Definition iffT (A B : Type) := ((A -> B) * (B -> A))%type.

(** We allow to unfold the [crelation] definition while doing morphism search. *)

Section Defs.
  Universe u.
  Context {A : Type@{u}}.

  (** We rebind crelational properties in separate classes to be able to overload each proof. *)

  Class Reflexive (R : crelation A) :=
    reflexivity : forall x : A, R x x.

  Definition complement@{ur} (R : crelation@{u ur} A) : crelation@{u ur} A :=
    fun x y => R x y -> False.

  (** Opaque for proof-search. *)
  Typeclasses Opaque complement iffT.
  
  (** These are convertible. *)
  Lemma complement_inverse@{v} (R : crelation@{u v} A) : complement (flip@{u u v+1} R) = flip@{u u v+1} (complement R).
  Proof. reflexivity. Qed.

  Class Irreflexive (R : crelation A) :=
    irreflexivity : Reflexive (complement R).

  Class Symmetric (R : crelation A) :=
    symmetry : forall {x y}, R x y -> R y x.
  
  Class Asymmetric (R : crelation A) :=
    asymmetry : forall {x y}, R x y -> complement R y x.
  
  Class Transitive (R : crelation A) :=
    transitivity : forall {x y z}, R x y -> R y z -> R x z.

  (** Various combinations of reflexivity, symmetry and transitivity. *)
  
  (** A [PreOrder] is both Reflexive and Transitive. *)

  Class PreOrder (R : crelation A)  := {
    PreOrder_Reflexive :> Reflexive R | 2 ;
    PreOrder_Transitive :> Transitive R | 2 }.

  (** A [StrictOrder] is both Irreflexive and Transitive. *)

  Class StrictOrder (R : crelation A)  := {
    StrictOrder_Irreflexive :> Irreflexive R ;
    StrictOrder_Transitive :> Transitive R }.

  (** By definition, a strict order is also asymmetric *)
  Global Instance StrictOrder_Asymmetric `(StrictOrder R) : Asymmetric R.
  Proof. firstorder. Qed.

  (** A partial equivalence crelation is Symmetric and Transitive. *)
  
  Class PER (R : crelation A)  := {
    PER_Symmetric :> Symmetric R | 3 ;
    PER_Transitive :> Transitive R | 3 }.

  (** Equivalence crelations. *)

  Class Equivalence (R : crelation A)  := {
    Equivalence_Reflexive :> Reflexive R ;
    Equivalence_Symmetric :> Symmetric R ;
    Equivalence_Transitive :> Transitive R }.

  (** An Equivalence is a PER plus reflexivity. *)
  
  Global Instance Equivalence_PER {R} `(Equivalence R) : PER R | 10 :=
    { PER_Symmetric := Equivalence_Symmetric ;
      PER_Transitive := Equivalence_Transitive }.

  (** We can now define antisymmetry w.r.t. an equivalence crelation on the carrier. *)
  
  Class Antisymmetric eqA `{equ : Equivalence eqA} (R : crelation A) :=
    antisymmetry : forall {x y}, R x y -> R y x -> eqA x y.

  Class subrelation (R R' : crelation A) :=
    is_subrelation : forall {x y}, R x y -> R' x y.
  
  (** Any symmetric crelation is equal to its inverse. *)
  
  Lemma subrelation_symmetric@{ur} (R : crelation@{u ur} A) `(Symmetric R) : subrelation (flip R) R.
  Proof. hnf. intros x y H'. red in H'. apply symmetry. assumption. Qed.

  Section flip.
    Universe ur.
    Context {R : crelation@{u ur} A}.
  
    Lemma flip_Reflexive `{Reflexive@{ur} R} : Reflexive (flip@{u u ur+1} R).
    Proof. tauto. Qed.
    
    Program Definition flip_Irreflexive@{} : Irreflexive@{ur} R ->
      Irreflexive@{ur} (@flip@{u u ur+1} A A Type@{ur} R):=
      fun irr => irreflexivity (R:=R).
    
    Program Definition flip_Symmetric@{} `(Symmetric R) : Symmetric (@flip@{u u ur+1} A A Type@{ur} R) :=
      fun x y H => symmetry@{ur} (R:=R) H.
    
    Program Definition flip_Asymmetric@{} `(Asymmetric R) : Asymmetric (@flip@{u u ur+1} A A Type@{ur} R) :=
      fun x y H H' => asymmetry (R:=R) H H'.
    
    Program Definition flip_Transitive@{} `(Transitive R) : Transitive (@flip@{u u ur+1} A A Type@{ur} R) :=
      fun x y z H H' => transitivity (R:=R) H' H.

    Program Definition flip_Antisymmetric@{ueq} `(Antisymmetric eqA R) :
      Antisymmetric@{ueq ur} eqA (@flip@{u u ur+1} A A Type@{ur} R).
    Proof. firstorder. Qed.

    (** Inversing the larger structures *)

    Lemma flip_PreOrder@{} `(PreOrder R) : PreOrder@{ur} (@flip@{u u ur+1} A A Type@{ur} R).
    Proof. firstorder. Qed.

    Lemma flip_StrictOrder@{} `(StrictOrder R) : StrictOrder (@flip@{u u ur+1} A A Type@{ur} R).
    Proof. firstorder. Qed.

    Lemma flip_PER@{} `(PER R) : PER (@flip@{u u ur+1} A A Type@{ur} R).
    Proof. firstorder. Qed.

    Lemma flip_Equivalence@{} `(Equivalence R) : Equivalence (@flip@{u u ur+1} A A Type@{ur} R).
    Proof. firstorder. Qed.

  End flip.

  Section complement.
    Universe ur.
    Context {R : crelation@{u ur} A}.

    Definition complement_Irreflexive@{} `(Reflexive R)
      : Irreflexive (complement R).
    Proof. firstorder. Qed.

    Definition complement_Symmetric@{} `(Symmetric R) : Symmetric (complement R).
    Proof. firstorder. Qed.
  End complement.

  (** Rewrite crelation on a given support: declares a crelation as a rewrite
   crelation for use by the generalized rewriting tactic.
   It helps choosing if a rewrite should be handled
   by the generalized or the regular rewriting tactic using leibniz equality.
   Users can declare an [RewriteRelation A RA] anywhere to declare default
   crelations. This is also done automatically by the [Declare Relation A RA]
   commands. *)

  Class RewriteRelation (RA : crelation A).

  (** Any [Equivalence] declared in the context is automatically considered
   a rewrite crelation. *)
    
  Global Instance equivalence_rewrite_crelation `(Equivalence eqA) : RewriteRelation eqA.
  Defined.

  (** Leibniz equality. *)
  Section Leibniz.
    Global Instance eq_Reflexive : Reflexive@{Set} (@eq A) := @eq_refl A.
    Global Instance eq_Symmetric : Symmetric@{Set} (@eq A) := @eq_sym A.
    Global Instance eq_Transitive : Transitive@{Set} (@eq A) := @eq_trans A.
    
    (** Leibinz equality [eq] is an equivalence crelation.
        The instance has low priority as it is always applicable
        if only the type is constrained. *)
    
    Global Program Instance eq_equivalence : Equivalence@{Set} (@eq A) | 10.
  End Leibniz.
  
End Defs.

(** Default rewrite crelations handled by [setoid_rewrite]. *)
#[global]
Instance impl_rewrite_relation : RewriteRelation impl.
Defined.

#[global]
Instance iff_rewrite_relation : RewriteRelation iff.
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

Ltac solve_crelation :=
  match goal with
  | [ |- ?R ?x ?x ] => reflexivity
  | [ H : ?R ?x ?y |- ?R ?y ?x ] => symmetry ; exact H
  end.

#[global]
Hint Extern 4 => solve_crelation : crelations.

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

Ltac simpl_crelation :=
  unfold flip, impl, arrow ; try reduce ; program_simpl ;
    try ( solve [ dintuition ]).

Local Obligation Tactic := simpl_crelation.

(** Logical implication. *)

#[global]
Program Instance impl_Reflexive : Reflexive impl.
#[global]
Program Instance impl_Transitive : Transitive impl.

(** Logical equivalence. *)

#[global]
Instance iff_Reflexive@{} : Reflexive@{Set+1 Set} iff := iff_refl.
#[global]
Instance iff_Symmetric : Symmetric@{Set+1 Set} iff := iff_sym.
#[global]
Instance iff_Transitive : Transitive@{Set+1 Set} iff := iff_trans.

(** Logical equivalence [iff] is an equivalence crelation. *)

(* Lemma iff_equivalence : Equivalence@{Set+1 Set} iff. *)

#[global]
Program Instance iff_equivalence : Equivalence@{Set+1 Set} iff.
#[global]
Program Instance arrow_Reflexive@{u} : Reflexive@{u+1 u} arrow@{u u}.
#[global]
Program Instance arrow_Transitive@{u} : Transitive@{u+1 u} arrow@{u u}.

#[global]
Instance iffT_Reflexive@{u} : Reflexive@{u+1 u} iffT@{u u}.
Proof. firstorder. Defined.
#[global]
Instance iffT_Symmetric@{u} : Symmetric@{u+1 u} iffT@{u u}.
Proof. firstorder. Defined. 
#[global]
Instance iffT_Transitive@{u} : Transitive@{u+1 u} iffT@{u u}.
Proof. firstorder. Defined.

(** We now develop a generalization of results on crelations for arbitrary predicates.
   The resulting theory can be applied to homogeneous binary crelations but also to
   arbitrary n-ary predicates. *)

Local Open Scope list_scope.

(** A compact representation of non-dependent arities, with the codomain singled-out. *)

(** We define the various operations which define the algebra on binary crelations *)
Section Binary.
  Universe u.
  Context {A : Type@{u}}.

  Definition relation_equivalence : crelation (crelation A) :=
    fun R R' => forall x y, iffT (R x y) (R' x y).

  Global Instance: RewriteRelation relation_equivalence.
  Defined.

  Definition relation_conjunction (R : crelation A) (R' : crelation A) : crelation A :=
    fun x y => prod (R x y) (R' x y).

  Definition relation_disjunction (R : crelation A) (R' : crelation A) : crelation A :=
    fun x y => sum (R x y) (R' x y).
  
  (** Relation equivalence is an equivalence, and subrelation defines a partial order. *)

  Global Instance relation_equivalence_equivalence :
    Equivalence relation_equivalence.
  Proof.
    split; red; unfold relation_equivalence, iffT.
    - firstorder.
    - firstorder.
    - intros x y z X X0 x0 y0. specialize (X x0 y0). specialize (X0 x0 y0). firstorder.
  Qed.
    
  Global Instance relation_implication_preorder : PreOrder (@subrelation A).
  Proof. firstorder. Qed.

  (** *** Partial Order.
   A partial order is a preorder which is additionally antisymmetric.
   We give an equivalent definition, up-to an equivalence crelation
   on the carrier. *)

  Class PartialOrder@{ur ur'} (eqA : crelation@{u ur} A) `{equ : Equivalence A eqA}
    (R : crelation@{u ur} A) `{preo : PreOrder A R} :=
    partial_order_equivalence : relation_equivalence@{ur' ur' ur} eqA
      (relation_conjunction@{ur ur ur} R (@flip@{u u ur+1} A A Type@{ur} R)).
  
  (** The equivalence proof is sufficient for proving that [R] must be a
   morphism for equivalence (see Morphisms).  It is also sufficient to
   show that [R] is antisymmetric w.r.t. [eqA] *)

  Global Instance partial_order_antisym `(PartialOrder eqA R) : Antisymmetric eqA R.
  Proof with auto.
    reduce_goal.
    firstorder.
  Qed.

  Lemma PartialOrder_inverse@{ur ur'} (eqA : crelation@{u ur} A) (r : crelation@{u ur} A)
     `(PartialOrder@{ur ur'} eqA R) : PartialOrder eqA (@flip@{u u ur+1} A A Type@{ur} R).
  Proof.
    firstorder.
  Qed.
End Binary.

#[global]
Hint Extern 3 (PartialOrder (flip _)) => class_apply PartialOrder_inverse : typeclass_instances.

(** The partial order defined by subrelation and crelation equivalence. *)

(* Program Instance subrelation_partial_order : *)
(*   ! PartialOrder (crelation A) relation_equivalence subrelation. *)
(* Obligation Tactic := idtac. *)

(* Next Obligation. *)
(* Proof. *)
(*   intros x. refine (fun x => x). *)
(* Qed. *)

Typeclasses Opaque relation_equivalence.


