From Coq.Properties Require Import GroupoidLaws.

Notation "f ∘ g" := (fun x => f (g x)) (at level 55).

Section Equivalence.
  Sorts sa sb.
  Universes a b.
  Context (A : Type@{sa|a}) (B: Type@{sb|b}).

  Record isEquiv (f : A -> B) := {
      sect : B -> A ;
      retr : B -> A ;
      sect_eq : f ∘ sect = id ;
      retr_eq : retr ∘ f = id ;
    }.

  Record equiv := { map :> A -> B ; map_is_equiv :> isEquiv map }.

End Equivalence.

Arguments sect {_ _ _} _.
Arguments retr {_ _ _} _.
Arguments sect_eq {_ _ _} _.
Arguments retr_eq {_ _ _} _.

Import GroupoidNotations.
Definition equiv_refl@{sa|a|} (A : Type@{sa|a}) : equiv A A :=
  {| map := id ; map_is_equiv := {| sect := id ; retr := id ; sect_eq := rfl ; retr_eq := rfl |} |}.


Definition equiv_trans@{sa sb sc|a b c|} (A : Type@{sa|a}) (B : Type@{sb|b}) (C : Type@{sc|c}) (AB : equiv A B) (BC : equiv B C) : equiv A C.
Proof.
  refine {| map := BC ∘ AB |}.
  simple refine {| sect := AB.(sect) ∘ BC.(sect) ; retr := AB.(retr) ∘ BC.(retr) |}.
  all: change ((?f1 ∘ ?f2) ∘ (?g2 ∘ ?g1)) with (f1 ∘ (f2 ∘ g2) ∘ g1).
  - rewrite sect_eq; apply sect_eq.
  - rewrite retr_eq; apply retr_eq.
Defined.