Module Type S.

  Parameter foo : Set.
  Definition bar := foo.

End S.

Module Type S'.

  Definition foo := nat.
  Definition id {A} (a:A) := a.

  Definition bar := id foo.

End S'.

Module Type EmptyT. End EmptyT.

Module Type FT (x:S') := EmptyT.

Module Foo (x:S).

End Foo.

Module Bar : FT := Foo.