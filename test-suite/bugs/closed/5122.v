Goal exists x, x.
  simple refine (ex_intro _ _ _); [..|simple refine (_ _)].
  simple refine (_ _).
  intro. refine x. intro x. refine True. refine True. refine I.
Qed.
