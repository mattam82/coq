(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * [Proper] instances for propositional connectives.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.

Local Obligation Tactic := try solve [simpl_relation | firstorder auto].

(** Standard instances for [not], [iff] and [impl]. *)

(** Logical negation. *)

#[global]
Program Instance not_impl_morphism@{s|?|?} :
  Proper (arrow --> arrow) not@{s|_} | 1.

Print not_impl_morphism.

#[global]
Program Instance not_iff_morphism@{s|?|} :
  Proper (iff ++> iff) not@{s|_}.

(** Logical conjunction. *)

#[global]
Program Instance and_impl_morphism@{s|?|} :
  Proper (arrow ==> arrow ==> arrow) prod@{s|_ _} | 1.

#[global]
Program Instance and_iff_morphism@{s|?|} :
  Proper (iff ==> iff ==> iff) prod@{s|_ _}.
Next Obligation.
  intros ? ? [? ?] ? ? [? ?]; split; intros [? ?]; split; eauto.
Qed.

(** Logical implication [impl] is a morphism for logical equivalence. *)

#[global]
Program Instance iff_iff_iff_impl_morphism@{s s'|?|} : Proper (iff ==> iff ==> iff) arrow@{s s'|_ _}.

(** Morphisms for quantifiers *)

About pointwise_relation.

#[global]
Program Instance ex_iff_morphism@{s s' s''|?|} {A : Type@{s|_}} : Proper (pointwise_relation@{s Type s'|_ _ _} A iff@{s'|_ _} ==> iff) (@sigma@{s s' s''|_ _} A).
Next Obligation.
compute. intros. firstorder. intros [? ?]; eexists; eauto. edestruct X; eauto.
Qed.

#[global]
Program Instance ex_flip_impl_morphism@{s|?|?} {A : Type@{s|_}} :
  Proper (pointwise_relation A (flip arrow) ==> flip arrow) (@sigmaR@{s|_ _} A) | 1.

#[global]
Program Instance all_iff_morphism@{s s'|?|} {A : Type@{s|_}} :
  Proper (pointwise_relation A iff ==> iff) (@all@{s s'|_ _} A).
Next Obligation.
intros A x y r.
constructor; intros H a;  apply r, H.
Qed.

#[global]
Program Instance all_impl_morphism {A : Type} :
  Proper (pointwise_relation A impl ==> impl) (@all A) | 1.

#[global]
Program Instance all_flip_impl_morphism {A : Type} :
  Proper (pointwise_relation A (flip impl) ==> flip impl) (@all A) | 1.

(** Equivalent points are simultaneously accessible or not *)

#[global]
Instance Acc_pt_morphism {A:Type}(E R : A->A->Prop)
 `(Equivalence _ E) `(Proper _ (E==>E==>iff) R) :
 Proper (E==>iff) (Acc R).
Proof.
  apply proper_sym_arrow_iff.
  - auto with relations.
  - intros x y EQ WF. apply Acc_intro; intros z Hz. assert (R z x). specialize (H0 z z (reflexivity _) _ _ EQ). destruct H0. eauto.
    apply Acc_inv with x; assumption.
Qed.

(** Equivalent relations have the same accessible points *)

#[global]
Instance Acc_rel_morphism {A:Type} :
 @Proper@{Type Prop|_ _} ((A -> A -> Prop) -> A -> Prop) (relation_equivalence ==> eq ==> iff@{Prop|_ _}) (@Acc A).
Proof.
  apply proper_sym_arrow_iff_2.
  - red. symmetry. assumption.
  - red. symmetry. assumption.
  - intros R R' EQ a a' Ha WF. subst a.
    induction WF as [x _ WF']. constructor.
    intros y Ryx. apply WF', EQ. assumption.
Qed.

About Acc_rel_morphism.

(** Equivalent relations are simultaneously well-founded or not *)

#[global]
Instance well_founded_morphism {A : Type} :
 Proper@{Type Prop|_ _} (relation_equivalence ==> iff) (@well_founded A).
Proof.
 unfold well_founded. intros x y r.
 constructor; intros H a.
 symmetry in r.
 apply (@Acc_rel_morphism A _ _ r a _ eq_refl), H.
 apply (@Acc_rel_morphism A _ _ r a _ eq_refl), H.
Qed.
