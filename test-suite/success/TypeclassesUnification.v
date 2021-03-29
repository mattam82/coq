Require Import ssreflect ssrbool.
Set Typeclasses Unification.
Require Import Classes.Init.
Set Primitive Projections.
Unset Printing Primitive Projection Parameters.
Require Import Arith.

Axiom cheat : forall {A}, A.
(** This calls the default unification algorithm to solve a constraint. *)
Global Hint Extern 0 (@Unify ?cum ?tyx ?tyy ?x ?y) =>
  progress (auto_conv cum x and y with typeclass_instances) :
  typeclass_instances.
Set Unification Stuck.


Module PureCSEq.
  (* This is a variant emulating canonical structure resolution through type-classes, in
      an entirely packed style. *)

  Module Equality.

    Class mixin_of (A : Type) := Mixin {
    op : A -> A -> bool;
    law : forall x y, reflect (x = y) (op x y) }.

    (** We index the mixing by its carrier: the carrier must be completely
      explicit to trigger a class query. *)
    Global Hint Mode mixin_of + : typeclass_instances.

    Structure type := Pack {
      sort :> Type;
      class : mixin_of sort
    }.

    Global Hint Extern 0 (mixin_of (sort ?X)) => exact (class X) : typeclass_instances.
  End Equality.

  Notation eqType := Equality.type.
  Coercion Equality.sort : Equality.type >-> Sortclass.

  Definition eq_op {T : eqType} : T -> T -> bool :=
    Equality.op (mixin_of := Equality.class T).

  Instance nat_eqMixin : Equality.mixin_of nat.
  Proof.
    refine (Equality.Mixin _ Nat.eqb _).
    intros x y.
    apply Bool.iff_reflect. apply cheat.
  Defined.

  Set Typeclasses Debug Verbosity 3.
  Set Debug "unification".
  Definition nat_eqType := {| Equality.sort := nat; Equality.class := nat_eqMixin |}.

  (** This is the general unification hint for canonical structures:
    we allow to destruct an evar for a record, when projected with
    an indexing projection. This results in typeclass for the rest of the
    fields (here a "Ring" evar) *)
  Local Hint Extern 0 (@Unify ?cum ?tyx ?tyy ?x ?y.(Equality.sort)) =>
    tryif is_evar y then
      instantiate (1 := ltac:(econstructor)); cbv beta iota
    else fail
    : typeclass_instances.

  (** The symmetric hint *)
  Local Hint Extern 0 (@Unify ?cum ?tyy ?tyx ?y.(Equality.sort) ?x) =>
    tryif is_evar y then
      instantiate (1 := ltac:(econstructor)); cbv beta iota
    else fail
    : typeclass_instances.

  (* Goal exists T, Unify false (Equality.sort T) nat.
  Proof.
    eexists.
    match goal with *)

  (* Lemma eq_over (x : nat) : eq_op x x. *)

  Lemma eqnE : Nat.eqb = eq_op.
  Proof. reflexivity. Qed.

  Set Typeclasses Debug Verbosity 3.

  Infix "==" := eq_op (at level 90).

  Lemma eq_op_refl {A : eqType} (x : A) : x == x.
  Proof.
    rewrite /eq_op. case: (Equality.law x x); auto.
  Qed.

  (** This finds ring directly, no resolution needed *)
  Goal forall x y : nat, x + y == y + x.
  Proof.
    intros. rewrite Nat.add_comm.
    apply eq_op_refl.
  Qed.

End PureCSEq.

Module PureCS.
(* This is a variant emulating canonical structure resolution through type-classes, in
    an entirely packed style. *)

  Class Ring (A : Type) := {
    ringOp : A -> A -> A;
    ringUnit : A;
    ringUnitLeft x : ringOp ringUnit x = x
  }.

  (** We index rings by their carrier: the carrier must be completely
    explicit to trigger a class query. *)
  Local Hint Mode Ring + : typeclass_instances.

  Structure ring := mkRing {
    sort :> Type;
    class : Ring sort
  }.

  Local Hint Extern 0 (Ring (@sort ?X)) => exact (class X) : typeclass_instances.

  Definition ring_class (r : ring) : Ring (sort r) := (class r).

  Definition nat_ring : Ring nat :=
    {| ringOp := plus;
       ringUnit := 0;
       ringUnitLeft := fun x => eq_refl |}.

  Definition ring_nat :=
  {| sort := nat; class := nat_ring |}.

  Set Typeclasses Debug Verbosity 3.

  Definition ring_op {r : ring} : r -> r -> r := ringOp.
  Definition ring_unit {r : ring} : r := ringUnit.
  Infix "⋅" := ring_op (at level 50) : ring_scope.
  Notation "'ε'" := ring_unit (at level 50) : ring_scope.
  Local Open Scope ring_scope.

  (** This finds ring directly, no resolution needed *)
  Goal forall x : ring_nat, (x + 0) = (x ⋅ 0).
  Proof.
    Set Printing All.
    reflexivity.
  Qed.

  (** This is the general unification hint for canonical structures:
    we allow to destruct an evar for a record, when projected with
    an indexing projection. This results in typeclass for the rest of the
    fields (here a "Ring" evar) *)
  Global Hint Extern 0 (@Unify ?cum ?tyx ?tyy ?x (sort ?y)) =>
    tryif is_evar y then
      instantiate (1 := ltac:(econstructor)); cbv beta delta [sort] iota
    else fail
    : typeclass_instances.

  (** The symmetric hint *)
  Global Hint Extern 0 (@Unify ?cum ?tyy ?tyx (sort ?y) ?x) =>
    tryif is_evar y then
      instantiate (1 := ltac:(econstructor)); cbv beta delta [sort] iota
    else fail
    : typeclass_instances.

  Section Default.
  Set Typeclasses Debug Verbosity 2.
  Existing Instance nat_ring.
  (** This finds `ring_nat` using nat_ring's default declaration. *)
  Goal forall x : nat, (x + 0) = (x ⋅ 0).
  Proof.
    Set Printing All.
    reflexivity.
  Qed.
  (* General lemma *)
  Goal forall x : nat, (0 + x) = x.
  Proof.
    intros x.
    apply: (ringUnitLeft x).
  Qed.

  End Default.

  Section NoDefault.
    (* If we don't declare a default nat instance, we get an unsolvable constraint *)
    Fail Goal forall x : nat, (x + 0) = (x ⋅ 0).
  End NoDefault.


  (** We generate a unification constraint
    sort ?X = nat and another
    cs_index ?X = t
    such that ?X needs to be refined with (mkRing _ _ _ ) first.

  *)

  Fixpoint ringpow {r : ring} (x : r) (n : nat) :=
    match n with
    | 0 => ε
    | S n => x ⋅ ringpow x n
    end.
  Set Printing Coercions.

  Existing Instance nat_ring.

  Goal forall x : nat, ringpow x 0 = 0.
  Proof. reflexivity. Qed.
End PureCS.


Module OperationalTypeclassesCS.
  (* This is a variant mixing operational typeclasses + a canonical structure *)
  Class RingOp A := { ring_op : A -> A -> A }.
  Class RingUnit A := { ring_unit : A }.

  Infix "⋅" := ring_op (at level 50) : ring_scope.
  Notation "'ε'" := ring_unit (at level 50) : ring_scope.
  Local Open Scope ring_scope.
  Class Ring (A : Type) := {
    ringOp :> RingOp A;
    ringUnit :> RingUnit A;
    ringUnitLeft x : ε ⋅ x = x
  }.
  (** We index rings by their carrier: they must be at least partially
    instantiated to trigger a query. *)
  Local Hint Mode Ring ! : typeclass_instances.

  Record ring := mkRing {
    sort :> Type;
    class : Ring sort
  }.

  Local Hint Extern 0 (Ring (@sort ?X)) =>
    tryif is_evar X then
      destruct X
    else
      exact (class X) : typeclass_instances.

  Definition ring_class (r : ring) : Ring (sort r) := (class r).

  Definition nat_ring : Ring nat :=
    {| ringOp := {| ring_op x y := x + y |};
      ringUnit := {| ring_unit := 0 |};
      ringUnitLeft := fun x => eq_refl |}.

  Definition ring_nat :=
    {| sort := nat; class := nat_ring |}.

  Set Typeclasses Debug Verbosity 3.

  (** This finds the class instance from the canonical structure *)
  Goal forall x : ring_nat, (x + 0) = (x ⋅ 0).
  Proof.
    Set Printing All.
    reflexivity.
  Qed.

  Section Default.


  Existing Instance nat_ring.
  (** This finds `ring_nat` using nat_ring's default declaration. *)
  Goal forall x : nat, (x + 0) = (x ⋅ 0).
  Proof.
    Set Printing All.
    reflexivity.
  Qed.
  (* General lemma *)
  Goal forall x : nat, (0 + x) = x.
  Proof.
    intros x.
    apply: (ringUnitLeft x).
  Qed.

  End Default.

  Section NoDefault.
    (* If we don't declare a default nat instance, we get an unsolvable constraint *)
    Fail Goal forall x : nat, (x + 0) = (x ⋅ 0).

  End NoDefault.

  (** We generate a unification constraint
    sort ?X = nat and another
    cs_index ?X = t
    such that ?X needs to be refined with (mkRing _ _ _ ) first. *)

  Fixpoint ringpow {r : ring} (x : r) (n : nat) :=
    match n with
    | 0 => ε
    | S n => x ⋅ ringpow x n
    end.
  Set Printing Coercions.

  (** This is the general unification hint for canonical structures:
    we allow to destruct an evar for a record, when projected with
    an indexing projection. This results in typeclass for the rest of the
    fields (here a "Ring" evar) *)
  Global Hint Extern 0 (@Unify ?cum ?tyx ?tyy ?x (sort ?y)) =>
    tryif is_evar y then
      instantiate (1 := ltac:(econstructor)); cbv beta delta [sort] iota
    else fail
    : typeclass_instances.

  (* The symmetric rule *)
  Global Hint Extern 0 (@Unify ?cum ?tyy ?tyx (sort ?y) ?x) =>
    tryif is_evar y then
      instantiate (1 := ltac:(econstructor)); cbv beta delta [sort] iota
    else fail
    : typeclass_instances.

  Existing Instance nat_ring.

  Goal forall x : nat, ringpow x 0 = 0.
  Proof. reflexivity. Qed.
End OperationalTypeclassesCS.
