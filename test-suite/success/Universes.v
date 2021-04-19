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
  Constraint u <= v.
  (* Constraint u <= w.
  Constraint w <= v. *)
  Constraint u+1 <= v.
  Print Universes "file.dot".
  Fail Constraint v <= u.
  Print Universes "file.dot".
End leleeq'.

Polymorphic Section compress.
  Universe x y z top.
  Print Universes "file.dot".
  Constraint x + 1 <= top.
  Print Universes "file.dot".
  Constraint z  <= x+1.
  Print Universes "file.dot".
  Constraint x <= y.
  Constraint y+1 <= z.
  Print Universes "file.dot".

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
  Print Universes "file.dot".
  Fail Constraint w <= v.
  Print Universes "file.dot".
  Check Constraint v+1 <= w.
  Check Constraint v <= w.
End leleeq'.

Polymorphic Section succtheory.
  Universe u v w.
  Print Universes "file.dot".
  Constraint u + 1 <= w.
  Print Universes "file.dot".
  Constraint v + 1 <= w.
  Print Universes "file.dot".
  Constraint u = v.
  Print Universes "file.dot".
  Check Constraint v = u.
  Print Universes "file.dot".

  Fail Constraint u = w.
  Print Universes "file.dot".
  Fail Constraint w = u.
  Print Universes "file.dot".
End succtheory.

Polymorphic Section succtheory.
  Universe u v w x.
  Print Universes "file.dot".
  Constraint u + 1 <= w.
  Print Universes "file.dot".
  Constraint x <= u + 1.
  Print Universes "file.dot".
  Constraint u <= v.
  Constraint v <= u.
  Print Universes "file.dot".
  Constraint u+1 <= x.
  Print Universes "file.dot".

  Constraint w <= u+1.
  Print Universes "file.dot".
  Constraint v <= w + 1.
  Print Universes "file.dot".
End succtheory.

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

Polymorphic Section eqset1.
  Universe u.
  Print Universes "file.dot".
  Constraint u <= Set+1.
  Print Universes "file.dot".
  Constraint Set+1 <= u.
  Print Universes "file.dot".
End eqset1.

Polymorphic Section leleeq.
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
End leleeq.


Polymorphic Section myset.
  Universe myset.
  Universe u.
  Print Universes "file.dot".
  Constraint myset <= Set+1.
  Print Universes "file.dot".
  Constraint u + 1 <= myset.
  Print Universes "file.dot".
  Constraint u <= Set.
  Print Universes "file.dot".
  Constraint u + 1 <= Set+1.
  Print Universes "file.dot".
End myset.

Polymorphic Section Big.
Universes u1 u2 u3.
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
(* Constraint u1 <= Set+1. *)
Print Universes "file.dot".
(* Constraint u2 <= Prop. *)
Print Universes "file.dot".

(* Fail Constraint u < v. *)
(* Fail Constraint u < v + 2. *)
(* Fail Constraint u + 2 < v. *)

End Big.

Polymorphic Section LargeLe.
  Universes u1 u2 u3.
  Constraint u2 = u1 + 1.
  Constraint u3 = u2 + 1.
  Print Universes "file.dot".
  Constraint u2 <= u3. (* Implied, no change *)
  Print Universes "file.dot".
  Constraint u1 <= u3.
  Constraint u1 < u3.
  Print Universes "file.dot".
  Fail Constraint u1 = u3.
End LargeLe.

Polymorphic Section Plus2.
  Universes x y k l.

  Constraint x + 2 <= k.
  Print Universes "file.dot".
  Constraint x <= y.
  Print Universes "file.dot".
  Constraint y + 2 <= k.
  Print Universes "file.dot".
  Constraint y + 1 <= l.
  Print Universes "file.dot".
  Constraint y + 1 <= x+1.
  Print Universes "file.dot".
  Check Constraint x + 1 = y + 1.
End Plus2.

Polymorphic Section Plus2.
Universes x y k l m.

Constraint x + 2 <= k.
Print Universes "file.dot".
Constraint x <= y.
Print Universes "file.dot".
Constraint y + 2 <= k.
Print Universes "file.dot".
Constraint y + 2 <= m.
Print Universes "file.dot".
Constraint x + 1 <= m.
Print Universes "file.dot".
Constraint m <= x + 1.
End Plus2.


Polymorphic Section Plus2Alias.
Universes x y k l m.

Constraint x + 2 <= k.
Print Universes "file.dot".
Constraint x <= y.
Print Universes "file.dot".
Constraint y + 2 <= k.
Print Universes "file.dot".
Constraint y + 1 <= l.
Constraint y + 2 <= m.
Print Universes "file.dot".
Constraint m <= x+2.
Print Universes "file.dot".
Check Constraint x + 1 = y + 1.
End Plus2.
