Require Import Setoid.

Parameter value' : Type.
Parameter equiv' : value' -> value' -> Prop.

Fail Add Parametric Relation : _ equiv'
  reflexivity proved by (Equivalence.equiv_reflexive _)
  transitivity proved by (@Equivalence.equiv_transitive _ _ _)
    as apply_equiv'_rel.
