Class A := {}.
  Class B {T} `(A) := { B_intro : forall t t' : T, t = t' }.
  Lemma foo T (t t' : T) : t = t'.
    erewrite [t]@B_intro. 
    reflexivity.
  Abort.
