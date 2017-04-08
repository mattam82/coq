
Class Zero (A : Type) := zero : A.
Notation "0" := zero.
Class One (A : Type) := one : A.
Notation "1" := one.
Class Addition (A : Type) := addition : A -> A -> A.
Notation "_+_" := addition.
Notation "x + y" := (addition x y).
Class Multiplication {A B : Type} := multiplication : A -> B -> B.
Notation "_*_" := multiplication.
Notation "x * y" := (multiplication x y).
Class Subtraction (A : Type) := subtraction : A -> A -> A.
Notation "_-_" := subtraction.
Notation "x - y" := (subtraction x y).
Class Opposite (A : Type) := opposite : A -> A.
Notation "-_" := opposite.
Notation "- x" := (opposite(x)).
Class Equality {A : Type}:= equality : A -> A -> Prop.
Notation "_==_" := equality.
Notation "x == y" := (equality x y) (at level 70, no associativity).
Class Bracket (A B: Type):= bracket : A -> B.
Notation "[ x ]" := (bracket(x)).
Class Power {A B: Type} := power : A -> B -> A.
Notation "x ^ y" := (power x y).

Require Import Morphisms.
Instance: Params (@bracket) 3 := {}.
Instance: Params (@equality) 2 := {}.
Instance: Params (@power) 3 := {}.
