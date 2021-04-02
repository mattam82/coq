Polymorphic Section leleeq.
  Universe u v.
  Print Universes "file.dot".
  Constraint u <= v.
  Print Universes "file.dot".
  Constraint v <= u.
  Print Universes "file.dot".
End leleeq.

Polymorphic Section leqset'.
  Universe u.
  Print Universes "file.dot".
  Constraint u <= Set.
  Print Universes "file.dot".
  Fail Constraint Set <= Prop.
  Print Universes "file.dot".
  Fail Constraint u <= Prop.
  Print Universes "file.dot".
End leqset'.

Polymorphic Section leleeq'.
  Universe u v w.
  Print Universes "file.dot".
  Constraint u  <= v + 1.
  Print Universes "file.dot".
  Constraint v  <= w.
  Print Universes "file.dot".
  Constraint w <= v+1.
  Print Universes "file.dot".
  Constraint v < w.
  Fail Constraint w + 1 <= v + 1.
  Print Universes "file.dot".
End leleeq'.

Polymorphic Section leleeq'.
  Universe u v w k k'.
  Print Universes "file.dot".
  Constraint w + 2 <= u.
  Print Universes "file.dot".
  Constraint v <= u + 1.
  Print Universes "file.dot".
  Constraint u < k.
  Print Universes "file.dot".
  Constraint k' <= u + 1.
  Print Universes "file.dot".
  Constraint k <= u + 1.


  Constraint u <= Set+1.
  Print Universes "file.dot".

  Constraint v + 1 <= u.
  Print Universes "file.dot".
  Fail Constraint v + 2 <= u.
  Print Universes "file.dot".
End leleeq'.

Polymorphic Section leqset.
  Universe u.
  Print Universes "file.dot".
  Constraint u <= Set.
  Print Universes "file.dot".
  Check ((fun x : Type@{u} => x) : forall (_ : Set), Set).
End leqset.

Polymorphic Section leq2scompat.
  Universe u v.
  Print Universes "file.dot".
  Constraint u <= v.
  Constraint v <= Set.
  Print Universes "file.dot".
End leq2scompat.

Polymorphic Section eqset.
  Universe u.
  Print Universes "file.dot".
  Constraint u <= Set+1.
  Print Universes "file.dot".
  Constraint Set+1 <= u.
  Print Universes "file.dot".


Universe u v w.
  Constraint u <= v.
  Constraint v <= w.
  Print Universes "file.dot".
  Constraint Set+1 = u.
  Print Universes "file.dot".

  Constraint Set+1 <= v.
  Print Universes "file.dot".
  Fail Constraint Set = v.
  Fail Constraint Set = w.
  Constraint Set+1 = w.
  Print Universes "file.dot".



  Constraint Set <= u.
  Print Universes "file.dot".
  Constraint u <= Set+1.
  Print Universes "file.dot".
  Constraint w <= Set+2.
  Print Universes "file.dot".


  Constraint w <= Set+2.
  Print Universes "file.dot".
  Constraint w <= Prop.
  Print Universes "file.dot".

End leleeq.


Module myset.
  Universe myset.
  Universe u.
  Print Universes "file.dot".
  Constraint myset <= Set+1.
  Print Universes "file.dot".
  Constraint u + 1 <= myset.
  Print Universes "file.dot".

End myset.*)

Module Big.
Universes u1 u2 u3.
Constraint u1 <= Set.
Print Universes "file.dot".



Constraint u1 <= u2 + 1.

Constraint u2 + 1 <= u3.
(* Constraint u2 < u4. *)

(* Print Universes Subgraph (u1 u2 u3 u4 u5) "file.dot".
Constraint u3 = u4.
Constraint u4 < u5. *)
Print Universes "file.dot".
Constraint u2 + 1 = u3.
Print Universes "file.dot".

Constraint u2 + 1 = u1.
Print Universes "file.dot".
Constraint u2 + 1 = u3.
Print Universes "file.dot".
Constraint u1 <= Set+1.
Print Universes "file.dot".
Constraint u2 <= Prop.
Print Universes "file.dot".

(* Fail Constraint u < v. *)
(* Fail Constraint u < v + 2. *)
(* Fail Constraint u + 2 < v. *)

End Big.

Module LargeLe.
  Universes u1 u2 u3.
  Constraint u2 = u1 + 1.
  Constraint u3 = u2 + 1.

  Print Universes Subgraph (u1 u2 u3) "file.dot".
  Constraint u2 <= u3. (* Implied, no change *)
  Constraint u1 <= u3.
  Constraint u1 < u3.
  Print Universes Subgraph (u1 u2 u3) "file.dot".
  Fail Constraint u1 = u3.

End LargeLe.



  Constraint u2 <= u1 + 2.
  Print Universes Subgraph (u1 u2 u3) "file.dot".
  Constraint u1 <= u2 + 1.



Constraint v + 3 <= w + 1.

(* (* Constraint z + 4 <= w + 5.
Constraint y + 4 <= w + 5. *)
Constraint y + 4 <= w + 5. *)

Print Universes Subgraph (u v w x y z) "file.dot".
