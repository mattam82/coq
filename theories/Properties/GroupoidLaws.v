From Coq Require Import PreludeOptions.
From Coq Require Import Types.

Set Printing Universes.

Section GroupoidOperations.
  Sort sa se.
  Universe a.
  Context {A : Type@{sa|a}}.
  Notation "x = y" := (eq@{_ se|_} x y) : type_scope.

  Definition inv {x y : A} : x = y -> y = x.
  Proof.
    intros e; induction e using eq_poly; reflexivity.
  Defined.

  Definition concat {x y z : A} : x = y -> y = z -> x = z.
  Proof.
    intros e; induction e using eq_poly; trivial.
  Defined.

  Definition tr@{b|} {B : Type@{sa|b}} (e : @eq@{_ sa|_} Type@{sa|max(a,b)} A B) : A -> B.
  Proof.
    induction e using eq_poly@{_ sa|max(a+1,b+1) max(a,b)}; trivial.
  Defined.

  Sort sb.
  Definition ap@{b|} {B : Type@{sb|b}} (f : A -> B) {x y : A} :
    x = y -> f x = f y.
  Proof.
    intros e ; induction e using eq_poly; reflexivity.
  Defined.

End GroupoidOperations.

Module GroupoidNotations.
Notation rfl := (ltac:(reflexivity)).

Notation " e ▷ t " := (ltac:(exact (tr e t) + exact (tr (inv e) t))) (at level 70).

Notation "e1 @ e2" := (concat e1 e2) (at level 65, right associativity).
End GroupoidNotations.
Import GroupoidNotations.

Section GroupoidLaws.
  Sort sa se.
  Universe a.
  Context {A : Type@{sa|a}}.
  Notation "x = y" := (eq@{_ se|_} x y) : type_scope.

  Definition lunit {x y : A} (e : x = y) : rfl @ e = e.
  Proof. reflexivity. Defined.

  Definition runit {x y : A} (e : x = y) : e @ rfl = e.
  Proof. induction e using eq_poly ; reflexivity. Defined.

  Definition assoc {x y z w : A} (e1 : x = y) (e2 : y = z) (e3 : z = w) :
    e1 @ e2 @ e3 = (e1 @ e2) @ e3.
  Proof. induction e1 using eq_poly; reflexivity. Defined.

  Definition inv_refl {x : A} : inv rfl = rfl :> (x = x).
  Proof. reflexivity. Defined.

  Definition inv_concat {x y z : A} (e : x = y) (e' : y = z) :
    inv (e @ e') = inv e' @ inv e.
  Proof.
    induction e using eq_poly; induction e' using eq_poly; reflexivity.
  Defined.

  Definition inv_inv {x y : A} (e : x = y) : inv (inv e) = e.
  Proof.
    induction e using eq_poly; reflexivity.
  Defined.

  Sort sb.
  Universe b.
  Context {B : Type@{sb|b}} (f : A -> B).

  Definition ap_rfl {x : A} : ap f rfl = rfl :> (f x = f x).
  Proof. reflexivity. Defined.

  Definition ap_concat {x y z : A} (e1 : x = y) (e2 : y = z) :
    ap f (e1 @ e2) = ap f e1 @ ap f e2.
  Proof.
    induction e1 using eq_poly; reflexivity.
  Defined.

  Definition ap_inv {x y : A} (e : x = y) : ap f (inv e) = inv (ap f e).
  Proof.
    induction e using eq_poly; reflexivity.
  Defined.

End GroupoidLaws.



