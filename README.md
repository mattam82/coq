All Your Base Are Belong to Us: Sort Polymorphism for Proof Assistants
======================================================================

Introduction
------------

This artefact is a modified version of Coq, based on commit
44155b062e6c384cc3ca36293b99dcd13f9cb085, taken between versions 8.19 and 8.20
(now out), and containing the changes of several other pull requests.

The upstream Coq repository can be found on the [coq GitHub
repo](https://github.com/coq/coq).

This version of Coq features, on the kernel and plugins side, an improved
compatibility with sort polymorphic developments, while its prelude has been
rewritten from scratch with sort polymorphic definitions.

Downloading this artefact
-------------------------

This artefact can be found at its stable DOI
[10.5281/zenodo.13939644](https://doi.org/10.5281/zenodo.13939644).


Building this artefact
----------------------
Usual Coq install instructions apply to this artefact. These can be found in the
file `INSTALL.md`. The OPAM switch method is recommended, with a small download
footprint, and we expect a build time of maximum 10 minutes on older machines.

### Building reproducibly
The dependencies needed for this version of Coq can be obtained reproducibly in
the future using [Guix](https://guix.gnu.org). A manifest file is provided to
that effect in `guix.scm`, along with a `channels.scm` file to pin the version
of Guix to a specific commit. One can then enter an environment with the
dependencies needed to build this project with
```bash
guix time-machine -C channels.scm -- shell -m guix.scm -- ./pre-inst-env "$SHELL"
```
From that point onwards, it is possible to use `make world` to build Coq, and
also launch `coqide` directly, the shell script `pre-inst-env` having set up
environment variables to use compiled binaries with installing them.

NB: Guix only supports GNU/Linux-based systems.

Using this artefact
-------------------

The new prelude is contained in `theories/`, and will be checked and compiled by
`make world`.  The tests for `setoid_rewrite` are contained in the file
`test-suite/success/setoid_test.v`.  You are encouraged to use CoqIDE, built
alongside Coq with `make coqide`, to browse and check the source yourself,
with the command `coqide`, as other interaction systems would need patches to
support this version of Coq. Some code specific to examples in the paper is
contained in `theories/Properties/SortPolyPaper.v`.

All Coq code in the paper starting from section 3 onwards is directly
transcluded from these files. They are always identified with enclosing comments
of the form
```coq
(** listings: IDENT **)

coq code

(** listings: end **)
```
where IDENT is an internal identifier used for transclusion in our LaTeX
sources. Here is a list of the snippets of Coq code in the order they appear in
the paper.

| Name             | Location                         | IDENT          |
|------------------|----------------------------------|----------------|
| empty            | Init.Types.Empty                 | empty          |
| unit             | Init.Types.Unit                  | unit           |
| bool             | Init.Types.Bool                  | bool           |
| true_false_sprop | Properties.SortPolyPaper         | true eq false  |
| sigma            | Init.Types.Sigma                 | sigma          |
| proj1            | Init.Types.Sigma                 | proj1          |
| sigmaR           | Init.Types.Sigma                 | sigmaR         |
| eq               | Init.Types.Equality              | eq             |
| eq_trans         | Init.Types.Equality              | eq_trans       |
| assoc            | Properties.GroupoidLaws          | eqassoc        |
| isEquiv          | Properties.Equivalence           | isEquiv        |
| relation         | Classes.Morphisms                | relation       |
| respectful       | Classes.Morphisms                | respectful     |
| respectful_per   | Classes.Morphisms                | respectful_per |
| same             | test-suite/success/setoid_test.v | same           |
| add_ext          | test-suite/success/setoid_test.v | add_ext        |
| P_ext            | test-suite/success/setoid_test.v | P_ext          |
| test_rewrite     | test-suite/success/setoid_test.v | test_rewrite   |
| LargeElimSort    | Properties.SortPolyPaper         | LargeElimSort  |
| neq_true_false   | Properties.SortPolyPaper         | neq true false |
| boolε            | Properties.SortPolyPaper         | bool param     |

All of these claims can be checked individually by loading the corresponding
files in CoqIDE after having built all of Coq with `make world`, and going
through the file using the Navigation menu, loading all relevant sentences in
the file.

Reviewers proficient in Coq are also encouraged to experiment using these new
definitions in their own simple examples: any new file outside of the
`theories/` subdirectory will automatically load the prelude.

Description of notable changes
------------------------------

### Prelude and standard library changes
The standard library was split out of the `theories` subdirectory using PR
[#19530](https://github.com/coq/coq/pull/19530). One of the main contributions
of the paper was then to rewrite the prelude (i.e. the remaining part of
`theories`) from scratch using sort and universe polymorphism. This includes the
definitions of basic inductive types, as well as support code for
setoid_rewrite.

The layout for this prelude is the following:
- `Init/Prelude.v` is the automatically-loaded prelude file used in normal Coq
  operation;
- `Init/Types/` contains definitions for each type, re-exported from a top-level
  `Init/Types.v` file;
- `Classes/` contains support code for setoid_rewrite.

### Kernel changes
Coq 8.19 already supports the core theory of sort polymorphism, with PRs
[#17836](https://github.com/coq/coq/pull/17836) and
[#18331](https://github.com/coq/coq/pull/18331).

On top of upstream, we also include
[#19537](https://github.com/coq/coq/pull/19537), which adds support for
algebraic universes in the kernel. This PR is in a polishing phase but is slated
for inclusion in Coq.

### Higher layers changes
We include [#18615](https://github.com/coq/coq/pull/18615) for easier
manipulation of sorts. Code for many tactics also had to be fixed, as it often
didn't support either sort-polymorphic definitions or even simply SProp.


Upstreaming status
------------------

Apart from the aforementioned open PRs, we plan on progressively isolating then
integrating the fixes for tactics and elaboration code in Coq.
