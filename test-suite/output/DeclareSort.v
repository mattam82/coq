Sort s.
Sort s'.

Fail Check fun (A:𝒰@{s;Set}) => A : 𝒰@{s';_}.

Fail Check fun (A:𝒰@{s;Set}) => A : Type.

Fail Check fun (A:Set) => A : 𝒰@{s;_}.

Check fun (A:𝒰@{s;Set}) => A : 𝒰@{s;_}.

Section S.
  Sort S1.
  Local Set Universe Polymorphism.
  Sort S2.

  Axiom foo : 𝒰@{S1;Set} -> 𝒰@{S2;Set}.
  Check foo.

End S.

About foo.
Set Printing Universes.
About foo.

Check foo : _ -> SProp.
Check foo : _ -> Set.

Fail Check foo : SProp -> _.
Fail Check foo : Set -> _.
Check foo : 𝒰@{S1;Set} -> Set.

Module Type T.
  Module M.
    Fail Sort foz.
  End M.
End T.
