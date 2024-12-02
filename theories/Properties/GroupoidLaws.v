From Corelib Require Import PreludeOptions.
From Corelib Require Import Types.

Set Printing Universes.

Module GroupoidNotations.
Notation rfl := (ltac:(cbn; reflexivity)) (only parsing).

Notation " e ▷ t " := (ltac:(exact (tr e t) + exact (tr (eq_sym e) t))) (at level 70, only parsing).

Notation "e1 ⋅ e2" := (eq_trans e1 e2) (at level 65, right associativity).
End GroupoidNotations.
Import GroupoidNotations.

Section GroupoidLaws.
  Sort sa se.
  Universe a.
  Context {A : Type@{sa|a}}.
  #[warnings="-notation-overridden"]
  Local Notation "x = y" := (eq@{_ se|_} x y) : type_scope.

  Definition lunit {x y : A} (e : x = y) : rfl ⋅ e = e.
  Proof. reflexivity. Defined.

  Definition runit {x y : A} (e : x = y) : e ⋅ rfl = e.
  Proof. induction e using eq_elim ; reflexivity. Defined.

(** listings: eqassoc **)
Definition assoc {x y z w : A} (e1 : x = y) (e2 : y = z) (e3 : z = w) :
    e1 ⋅ (e2 ⋅ e3) = (e1 ⋅ e2) ⋅ e3.
(** listings: end **)
Proof. induction e1 using eq_elim; reflexivity. Defined.

  Definition sym_lInv {x y : A} (e : x = y) : eq_sym e ⋅ e = rfl.
  Proof. induction e using eq_elim. reflexivity. Qed.

  Definition sym_rInv {x y : A} (e : x = y) : e ⋅ eq_sym e = rfl.
  Proof. induction e using eq_elim. reflexivity. Qed.

  Definition inv_refl {x : A} : eq_sym rfl = rfl :> (x = x).
  Proof. reflexivity. Defined.

  Definition inv_concat {x y z : A} (e : x = y) (e' : y = z) :
    eq_sym (e ⋅ e') = eq_sym e' ⋅ eq_sym e.
  Proof.
    induction e using eq_elim; induction e' using eq_elim; reflexivity.
  Defined.

  Definition sym_sym {x y : A} (e : x = y) : eq_sym (eq_sym e) = e.
  Proof.
    induction e using eq_elim; reflexivity.
  Defined.

  Sort sb.
  Universe b.
  Context {B : Type@{sb|b}} (f : A -> B).

  Definition ap_rfl {x : A} : ap f rfl = rfl :> (f x = f x).
  Proof. reflexivity. Defined.

  Definition ap_concat {x y z : A} (e1 : x = y) (e2 : y = z) :
    ap f (e1 ⋅ e2) = ap f e1 ⋅ ap f e2.
  Proof.
    induction e1 using eq_elim; reflexivity.
  Defined.

  Definition ap_eq_sym {x y : A} (e : x = y) : ap f (eq_sym e) = eq_sym (ap f e).
  Proof.
    induction e using eq_elim; reflexivity.
  Defined.

End GroupoidLaws.


