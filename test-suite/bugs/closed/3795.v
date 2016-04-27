Require Import Morphisms Program.Basics.
  Require Import Setoid.
  Definition foo := nat -> Prop.
  Parameter f : foo -> foo -> Prop.
  Parameter g : nat -> nat -> nat -> nat -> nat -> nat -> foo.
  Parameter b : nat.
  Axiom b_id : b = 0.
  Goal f
     (g 0 0 0 0 0 b)
     (g 0 0 0 0 0 b).
Time    setoid_rewrite b_id.    
Qed.