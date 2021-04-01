(*Module myset.
  Universe myset.
  Universe u.
  Print Universes "file.dot".
  Constraint myset <= Set+1.
  Set Printing Universes.
  Print Universes "file.dot".
  Fail Constraint u + 1 <= myset.
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
