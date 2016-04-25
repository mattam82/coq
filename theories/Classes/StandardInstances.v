(* Library added by Théo Zimmermann 2016 *)

Require Export Coq.Classes.CRespectful.

Lemma arrow_arrow : (iffT ##> iffT ##> iffT) arrow arrow.
Proof.
(*  firstorder. *)
  intros A B [f f'] C D [g g'].
  split; intros H1 H2.
  exact (g (H1 (f' H2))).
  exact (g' (H1 (f H2))).
Qed.

Lemma impl_impl : (iff ##> iff ##> iff) impl impl.
Proof ltac:(firstorder).

Lemma impl_impl' : (iff ##> iff ##> iffT) impl impl.
Proof ltac:(firstorder).

Lemma iff_iff : (iff ##> iff ##> iff) iff iff.
Proof ltac:(firstorder).

Lemma iff_iff' : (iff ##> iff ##> iffT) iff iff.
Proof ltac:(firstorder).

Lemma prod_prod : (iffT ##> iffT ##> iffT) prod prod.
Proof ltac:(firstorder).

Lemma and_and : (iff ##> iff ##> iff) and and.
Proof ltac:(firstorder).

Lemma and_and' : (iff ##> iff ##> iffT) and and.
Proof ltac:(firstorder).

Lemma or_or : (iff ##> iff ##> iff) or or.
Proof ltac:(firstorder).

Lemma or_or' : (iff ##> iff ##> iffT) or or.
Proof ltac:(firstorder).

Lemma eq_eq (A : Type) : (eq ##> eq ##> iff) (@eq A) (@eq A).
Proof.
  intros x x' Hx y y' Hy; split; intro Heq.
  + rewrite <- Hx, <- Hy.
    assumption.
  + rewrite Hx, Hy.
    assumption.
Qed.

Lemma eq_eq' (A : Type) : (eq ##> eq ##> iffT) (@eq A) (@eq A).
Proof.
  lazy beta delta.
  intros x x' Hx y y' Hy; split; intro Heq.
  now rewrite <- Hx, <- Hy.
  now rewrite Hx, Hy.
Qed.