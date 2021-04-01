Universes u1 u2 u3 u4 u5.
Constraint u1 <= u2 + 1.

Constraint u2 + 1 <= u3.
Constraint u2 < u4.

Print Universes Subgraph (u1 u2 u3 u4 u5) "file.dot".
Constraint u3 = u4.
Constraint u4 < u5.
Print Universes Subgraph (u1 u2 u3 u4 u5) "file.dot".

Constraint u2 + 1 = u1.
Print Universes Subgraph (u1 u2 u3 u4 u5) "file.dot".

(* Fail Constraint u < v. *)
(* Fail Constraint u < v + 2. *)
(* Fail Constraint u + 2 < v. *)


Constraint v + 3 <= w + 1.

(* (* Constraint z + 4 <= w + 5.
Constraint y + 4 <= w + 5. *)
Constraint y + 4 <= w + 5. *)

Print Universes Subgraph (u v w x y z) "file.dot".
