Definition foo1@{s| |} (A B :Type@{s|0}) (e : eq@{Type s|_} A B) : A -> B.
Proof.
  rewrite e; trivial.
Defined.

Definition foo2@{s|u |} (A :Type@{s|0}) {x y : A} (P : A -> Type@{s|u}) (e : x ≡ y) : P x -> P y.
Proof.
  rewrite e.
  trivial.
Defined.

Definition foo3@{s s'|u |} (A :Type@{s|0}) {x y : A} (P : A -> Type@{s'|u}) (e : x = y :> A) : P x -> P y.
Proof.
  rewrite e.
  trivial.
Defined.

Definition foo4@{s| |} (A B :Type@{s|0}) (e : A = B :> Type@{s|Set+1}) : A -> B.
Proof.
  rewrite e.
  trivial.
Defined.

Definition foo5 (A B : Type@{0}) (e : A = B) : A -> B.
Proof.
  rewrite e.
  trivial.
Defined.

Definition foo6 (A B : Type@{0}) (e : A = B :> _ : SProp) : A -> B.
Proof.
  rewrite e.
  trivial.
Defined.
