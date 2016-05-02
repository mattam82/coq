(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * [Proper] instances for propositional connectives.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Relation_Definitions.
Local Obligation Tactic := try solve [simpl_relation | firstorder auto].

Instance respectul_pointwise_subrelation A B (R : relation B) :
  subrelation (@eq A ==> R)%signature (pointwise_relation A R).
Proof. reduce. apply H. reflexivity. Qed.

Instance pointwise_subrelation_respectful A B (R : relation B) :
  subrelation (pointwise_relation A R) (@eq A ==> R)%signature.
Proof. reduce. subst x0. eapply H. Qed.

(** Standard instances for [not], [iff] and [impl]. *)

(** Logical negation. *)

Program Instance not_impl_morphism :
  Proper (impl --> impl) not | 1.

Program Instance not_iff_morphism :
  Proper (iff ++> iff) not.

(** Logical conjunction. *)

Program Instance and_impl_morphism :
  Proper (impl ==> impl ==> impl) and | 1.

Program Instance and_iff_morphism :
  Proper (iff ==> iff ==> iff) and.

(** Logical disjunction. *)

Program Instance or_impl_morphism :
  Proper (impl ==> impl ==> impl) or | 1.

Program Instance or_iff_morphism :
  Proper (iff ==> iff ==> iff) or.

(** Logical implication [impl] is a morphism for logical equivalence. *)

Program Instance iff_iff_iff_impl_morphism : Proper (iff ==> iff ==> iff) impl.

(** Morphisms for quantifiers *)

Program Instance ex_iff_morphism {A : Type} :
  Proper (pointwise_relation A iff ==> iff) (@ex A).

Program Instance ex_impl_morphism {A : Type} :
  Proper (pointwise_relation A impl ==> impl) (@ex A) | 1.

Program Instance ex_flip_impl_morphism {A : Type} :
  Proper (pointwise_relation A (flip impl) ==> flip impl) (@ex A) | 1.

Instance ex_eq_morphism {A : Type} :
  Proper (pointwise_relation A Logic.eq ==> iff) (@ex A) | 2.
Proof.
  unfold Proper. intros f g eqfg. red in eqfg.
  split. intros [x fx]. exists x. now rewrite <- eqfg.
  intros [x fx]; exists x; now rewrite eqfg.
Qed.

Instance ex_R_iff_morphism {A : Type} {R} (HR : Reflexive R) :
  Proper ((R ==> iff) ==> iff) (@ex A) | 2.
Proof.
  unfold Proper. intros f g eqfg. red in eqfg.
  split. intros [x fx]. exists x. rewrite <- eqfg. apply fx. reflexivity.
  intros [x fx]; exists x; rewrite eqfg. apply fx. reflexivity.
Qed.

Instance all_R_iff_morphism {A : Type} {R} (HR : Reflexive R) :
  Proper ((R ==> iff) ==> iff) (@all A) | 2.
Proof.
  unfold Proper. intros f g eqfg. red in eqfg.
  split. intros af x. rewrite <- eqfg. apply af. reflexivity.
  intros ag x; rewrite eqfg. apply ag. reflexivity.
Qed.

Instance all_hetero_R_iff_morphism {A : Type} {R} (HR : Reflexive R) :
  Proper ((∀ _ : R _ _, iff) ==> iff) (@all A) | 2.
Proof.
  unfold Proper. intros f g eqfg. red in eqfg.
  split. intros af x. rewrite <- eqfg. apply af. reflexivity.
  intros ag x; rewrite eqfg. apply ag. reflexivity.
Qed.

Program Instance all_iff_morphism {A : Type} :
  Proper (pointwise_relation A iff ==> iff) (@all A).

Program Instance all_impl_morphism {A : Type} :
  Proper (pointwise_relation A impl ==> impl) (@all A) | 1.

Program Instance all_flip_impl_morphism {A : Type} :
  Proper (pointwise_relation A (flip impl) ==> flip impl) (@all A) | 1.

Instance all_eq_morphism {A : Type} :
  Proper (pointwise_relation A Logic.eq ==> iff) (@all A) | 2.
Proof.
  unfold Proper, all. intros f g eqfg. red in eqfg.
  split. intros x y; now rewrite <- eqfg.
  intros x y; now rewrite eqfg.
Qed.

(** Equivalent points are simultaneously accessible or not *)

Instance Acc_pt_morphism {A:Type}(E R : A->A->Prop)
 `(Equivalence _ E) `(Proper _ (E==>E==>iff) R) :
 Proper (E==>iff) (Acc R).
Proof.
 apply proper_sym_impl_iff; auto with *.
 intros x y EQ WF. apply Acc_intro; intros z Hz.
rewrite <- EQ in Hz. now apply Acc_inv with x.
Qed.

(** Equivalent relations have the same accessible points *)

Instance Acc_rel_morphism {A:Type} :
 Proper (relation_equivalence ==> Logic.eq ==> iff) (@Acc A).
Proof.
 apply proper_sym_impl_iff_2. red; now symmetry. red; now symmetry.
 intros R R' EQ a a' Ha WF. subst a'.
 induction WF as [x _ WF']. constructor.
 intros y Ryx. now apply WF', EQ.
Qed.

Definition related_proper {A} R (m : A) : Related R m m -> @Proper A R m :=
  fun x => x.

Ltac solve_related :=
  match goal with
  |- Proper _ _ => apply related_proper; typeclasses eauto
  end.

Import ProperNotations.
Local Open Scope signature_scope.
(* Instance related_forall {A : Type} (B : A -> Prop) (B' : A -> Prop) : *)
(*   (forall x y, Related iff (B x) (B' y)) -> *)
(*   Related iff (forall x : A, B x) (forall y : A, B' y). *)
(* Proof. firstorder. Defined. *)

Instance related_forall {A : Type} (B : A -> Prop) (B' : A -> Prop) R (S : Prop -> Prop -> Prop) :
  Related (pointwise_relation A R) B B' ->
  Proper (pointwise_relation A R ==> S) (@all A) ->
  Related S (forall x : A, B x) (forall y : A, B' y).
Proof. firstorder. Defined.

(** Equivalent relations are simultaneously well-founded or not *)
Instance well_founded_morphism {A : Type} :
 Proper (relation_equivalence ==> iff) (@well_founded A).
Proof. 
  unfold well_founded.
  solve_proper. (* solve_related. *)
Qed.

(* To sort *)

Class IsEquiv {A B} (f : A -> B) :=
  { inv : B -> A;
    sect : forall x, f (inv x) = x;
    retr : forall x, inv (f x) = x }.

Hint Resolve sect retr.

Instance is_equiv_id {A : Type} : IsEquiv (@id A).
Proof.
  refine {| inv := id |}; reflexivity. 
Defined.

Require Import ProofIrrelevance.

Lemma iff_related_proj1 {A B : Prop} (p : Related iff A B) : A -> B.
  now destruct p. 
Defined.

Lemma iff_related_proj2 {A B : Prop} (p : Related iff A B) : B -> A.
  now destruct p. 
Defined.

Instance is_equiv_prop {A B : Prop} (p : Related iff A B) : IsEquiv (iff_related_proj1 p).
Proof.
  refine {| inv := proj2 p |}; intros; apply proof_irrelevance.
Defined.

Definition IsEquiv_rel {A B} f {I : @IsEquiv A B f} : A -> B -> Prop :=
  fun (p : A) (q : B) => f p = q /\ inv q = p.

Import ProperNotations.
Local Open Scope signature_scope.

Instance equiv_all_iff A B f (I : @IsEquiv A B f) :
  Related (∀ _ : (∀ _ : (IsEquiv_rel f) x y, iff) _ _, iff) (@all A) (@all B).
Proof.
  intros P P' rPP'.
  red in rPP'.
  unfold all; split; intros fall x. 
  - rewrite <- rPP';[apply (fall (inv x))|split].
    + apply sect.
    + auto.
  - rewrite rPP';[apply (fall (f x))|split].
    + trivial.
    + apply retr.
Qed.
Require Import Program.Basics.

Class HasSection {A B} (f : A -> B) :=
  { sinv : B -> A;
    ssect : forall x, f (sinv x) = x }.

Class HasRetraction {A B} (f : A -> B) :=
  { rinv : B -> A;
    rretr : forall x, rinv (f x) = x }.

Instance equiv_has_section A B f (I : @IsEquiv A B f) : HasSection f :=
  {| sinv := inv; ssect := sect |}.

Instance equiv_has_retraction A B f (I : @IsEquiv A B f) : HasRetraction f :=
  {| rinv := inv; rretr := retr |}.

Definition HasSection_rel {A B} f {I : @HasSection A B f} : A -> B -> Prop :=
  fun (p : A) (q : B) => f p = q /\ sinv q = p.

Definition HasRetraction_rel {A B} f {I : @HasRetraction A B f} : A -> B -> Prop :=
  fun (p : A) (q : B) => f p = q /\ rinv q = p.

Instance equiv_all_impl A B f (I : @HasSection A B f) :
  Related (∀ _ : (∀ _ : (HasSection_rel f) x y, impl) _ _, impl) (@all A) (@all B).
Proof.
  intros P P' rPP'.
  red in rPP'.
  unfold all; intros fall x. 
  - rewrite <- rPP';[apply (fall (sinv x))|split].
    + apply ssect.
    + auto.
Qed.

Instance equiv_all_flip_impl A B f (I : @HasRetraction A B f) :
  Related (∀ _ : (∀ _ : (HasRetraction_rel f) x y, flip impl) _ _, flip impl)
          (@all A) (@all B).
Proof.
  intros P P' rPP'.
  red in rPP'.
  unfold all; intros fall x. 
  - rewrite rPP';[apply (fall (f x))|split].
    + trivial.
    + apply rretr.
Qed.

Lemma eq_prop_related_proj1 {A B : Prop} (p : Related eq A B) : A -> B.
  now destruct p. 
Defined.

Lemma eq_prop_related_proj2 {A B : Prop} (p : Related eq A B) : B -> A.
  now destruct p. 
Defined.

Lemma eq_related_proj1 {A B : Type} (p : Related eq A B) : A -> B.
  now destruct p. 
Defined.

Lemma eq_related_proj2 {A B : Type} (p : Related eq A B) : B -> A.
  now destruct p. 
Defined.

Instance is_equiv_eq_type {A B : Type} (p : Related eq A B) :
  IsEquiv (eq_related_proj1 p).
Proof.
  destruct p. simpl. apply is_equiv_id.
Defined.

Instance is_equiv_eq_prop_type {A B : Prop} (p : Related eq A B) :
  IsEquiv (eq_prop_related_proj1 p).
Proof.
  destruct p. simpl. apply is_equiv_id.
Defined.

(*

Instance full_subrelation_equivalence A : Equivalence (full_relation A A).
Proof. firstorder. Defined.

Instance full_subrelation_subrelation A R : subrelation R (full_relation A A).
Proof. firstorder. Defined.

Instance full_subrelation_pointwise A B (R S : relation B) :
  subrelation S R ->
  subrelation (full_relation A A ==> S) (pointwise_relation A R).
Proof. firstorder. Defined.

Instance all_hetero_R_eq_morphism {A : Type} {R} {HR : Reflexive R} :
  Proper ((∀ _ : R _ _, @eq Prop) ==> iff) (@all A) | 2.
Proof.
  unfold Proper, all. intros f g eqfg. red in eqfg.
  split. intros x y. now erewrite <- (eqfg y).
  intros x y; now erewrite eqfg.
Qed.

Instance all_full_hetero_R_eq_morphism :
    Proper (∀ α : eq A A', (∀ _ : (∀ _ : (full_relation A A') _ _, @eq Prop) _ _, iff)) (@all) | 2.
Proof.
  unfold Proper, all. intros A A' -> f g eqfg.
  split. intros x' y'. red in eqfg. erewrite <- (eqfg y' y'). apply x'. red. exact I.
  intros. red in eqfg. erewrite (eqfg x x). apply H. exact I.
Qed.

Instance all_partialapp (T : Type) :
    Proper (∀ _ : (∀ _ : (full_relation T T) _ _, @eq Prop) _ _, iff) (@all T) | 2.
Proof.
  unfold Proper, all. intros f g eqfg.
  split. intros x' y'. red in eqfg. erewrite <- (eqfg y' y'). apply x'. red. exact I.
  intros. red in eqfg. erewrite (eqfg x x). apply H. exact I.
Qed.

*)