From Coq.Properties Require Import GroupoidLaws.

Notation "f ∘ g" := (fun x => f (g x)) (at level 55).

Section Equivalence.
  Sorts sa sb se.
  Universes a b.
  Context (A : Type@{sa|a}) (B: Type@{sb|b}).

  Record isEquiv (f : A -> B) := {
      sect : B -> A ;
      retr : B -> A ;
      sect_eq : forall b, eq@{_ se| _} (f (sect b)) b ;
      retr_eq : forall a, eq@{_ se| _} (retr (f a)) a ;
    }.

  Record equiv := { map :> A -> B ; map_is_equiv :> isEquiv map }.

End Equivalence.

Arguments sect {_ _ _} _.
Arguments retr {_ _ _} _.
Arguments sect_eq {_ _ _} _.
Arguments retr_eq {_ _ _} _.

Import GroupoidNotations.
Definition equiv_refl@{sa|a|} (A : Type@{sa|a}) : equiv A A :=
  {| map := id ; map_is_equiv := {| sect := id ; retr := id ; sect_eq := fun _ => eq_refl ; retr_eq := fun _ => rfl |} |}.


Definition equiv_trans@{sa sb sc|a b c|} (A : Type@{sa|a}) (B : Type@{sb|b}) (C : Type@{sc|c}) (AB : equiv A B) (BC : equiv B C) : equiv A C.
Proof.
  refine {| map := BC ∘ AB |}.
  simple refine {| sect := AB.(sect) ∘ BC.(sect) ; retr := AB.(retr) ∘ BC.(retr) |}.
  all: intros; cbn.
  - rewrite sect_eq; apply sect_eq.
  - rewrite retr_eq; apply retr_eq.
Defined.


Set Printing Universes.

Section SigmaAssoc.
  Sorts a b c.
  Universes a b c.
  Context (A : Type@{a|a}) (B : A -> Type@{b|b}) (C : forall a, B a -> Type@{c|c}).

  (* All Sigma types in Type *)
  Let T1 := Σ (a : A) (b : B a), C a b.
  Let T2 := Σ (p : Σ (a : A), B a), C (π1 p) (π2 p).

  Let f12 (t : T1) : T2 := let '(a, b, c) := t in ((a, b), c).
  Let f21 (t : T2) : T1 := let '((a,b), c) := t in (a, b, c).

  Let f12_is_equiv : isEquiv _ _ f12.
  Proof.
    refine {| sect := f21 ; retr := f21 |}.
    - intros [[a b] c]; reflexivity.
    - intros (a & b & c); reflexivity.
  Defined.

  Definition sigma_type_assoc : equiv T1 T2 :=
    {| map := f12 ; map_is_equiv := f12_is_equiv |}.
End SigmaAssoc.

Section SigmaAssocHom.
  Sorts s.
  Universes a b c.
  Context (A : Type@{s|a}) (B : A -> Type@{s|b}) (C : forall a, B a -> Type@{s|c}).

  (* All Sigma types in sort s *)
  Let T1 := sigma@{s s s|_ _} A (fun a => sigma@{s s s|_ _} (B a) (C a)).
  Let T2 := sigma@{s s s|_ _} (sigma@{s s s|_ _} A B) (fun p => C (projT1 p) (projT2 p)).

  Definition f12 (t : T1) : T2 := let '(a, b, c) := t in ((a, b), c).
  Definition f21 (t : T2) : T1 := let '((a,b), c) := t in (a, b, c).

  Definition f12_is_equiv : isEquiv@{s s s| _ _} _ _ f12.
  Proof.
    refine {| sect := f21 ; retr := f21 |}.
    - intros [[a b] c]; reflexivity.
    - intros (a & b & c); reflexivity.
  Defined.

  Definition sigma_hom_assoc : equiv T1 T2 :=
    {| map := f12 ; map_is_equiv := f12_is_equiv |}.
End SigmaAssocHom.
