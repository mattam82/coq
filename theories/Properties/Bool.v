From Coq Require Import Types.Bool.
From Coq Require Import Tactics.Ltac.

(** Basic properties of [andb] *)
Lemma andb_prop (a b:bool) : andb a b = true -> (a = true) * (b = true).
Proof.
  destruct a, b; repeat split; assumption.
Qed.
#[global]
Hint Resolve andb_prop: bool.

Register andb_prop as core.bool.andb_prop.

Lemma andb_prop_poly@{s| |} (a b:bool@{s|}) : andb a b ≡ true -> (a ≡ true) * (b ≡ true).
Proof.
  destruct a, b; repeat split; assumption.
Qed.
#[global]
Hint Resolve andb_prop_poly: bool.

(* Register andb_prop_poly as core.bool.andb_prop. *)

Lemma andb_true_intro (b1 b2 : bool) :
  (b1 = true) * (b2 = true) -> andb b1 b2 = true.
Proof.
  destruct b1; destruct b2; simpl; intros [? ?]; assumption.
Qed.
#[global]
Hint Resolve andb_true_intro: bool.

Register andb_true_intro as core.bool.andb_true_intro.

Lemma andb_true_intro_poly@{s| |} (b1 b2 : bool@{s|}) :
  (b1 ≡ true) * (b2 ≡ true) -> (andb b1 b2 ≡ true).
Proof.
  destruct b1; destruct b2; simpl; intros [? ?]; assumption.
Qed.
#[global]
Hint Resolve andb_true_intro_poly: bool.

(* Register andb_true_intro as core.bool.andb_true_intro. *)

(** Interpretation of booleans as propositions *)

Inductive eq_true@{s| |} : bool@{s|} -> Prop := is_eq_true : eq_true true.

#[global]
Hint Constructors eq_true : eq_true.

Register eq_true as core.eq_true.type.

(** Another way of interpreting booleans as propositions *)

Definition is_true b := b = true.

Definition is_true_poly@{s| |} (b : bool@{s|}) := b ≡ true.

(** [is_true] can be activated as a coercion by
   ([Local]) [Coercion is_true : bool >-> Sortclass].
*)

(** Additional rewriting lemmas about [eq_true] *)

Lemma eq_true_ind_r@{s| |} :
  forall (P : bool@{s|} -> Prop) (b : bool), P b -> eq_true b -> P true.
Proof.
  intros P b H H0; destruct H0 in H; assumption.
Defined.

Lemma eq_true_rect_r@{s|u|} :
  forall (P : bool@{s|} -> Type@{u}) (b : bool), P b -> eq_true b -> P true.
Proof.
  intros P b H H0; destruct H0 in H; assumption.
Defined.

(** The [BoolSpec] inductive will be used to relate a [boolean] value
    and two propositions corresponding respectively to the [true]
    case and the [false] case.
    Interest: [BoolSpec] behave nicely with [case] and [destruct].
    See also [Bool.reflect] when [Q = ~P].
*)

Inductive BoolSpec@{s| |} (P Q : Prop) : bool@{s|} -> Prop :=
  | BoolSpecT : P -> BoolSpec P Q true
  | BoolSpecF : Q -> BoolSpec P Q false.
#[global]
Hint Constructors BoolSpec : core.

Register BoolSpec as core.BoolSpec.type.
Register BoolSpecT as core.BoolSpec.BoolSpecT.
Register BoolSpecF as core.BoolSpec.BoolSpecF.
