Split presentation in two views:
- Mathematical/Computer Science user view
- Theoretical/insider/developer's view

More examples, incremental presentation: first usage, with a large
audience, then exhaustive technical explanations adressed to the
expert/developer. Attribute features to contacts/maintainers.

- Acknowledge the different views, e.g. on tactics: we don't want to run
into debates of alternative solutions here.

- Open ended / usage view

- Missing a detailed view of the system:
* How is it organized?
* What is the TCB?
  High-level and precisely
* How to review a Coq library (coqchk, printing)

- Missing a documentation of the elaboration process.

- constr:(), "Vernacular": really from the user point of view: terms,
  commands.


- Coq standard library introduction:
* TODO Actually introduce definitions and their usage with examples.
  How does it relate to stdlib2?

* Very long chapters, split them up, does sphinx allow that?

Ideal overall structure:

* Core calculus. PCuIC
-- No use of elaboration here! Actually should avoid using Gallina at
all. A checker should be able to do that.
** Summary/highlights
** Terms
*** Correspondance to actual Coq syntax (for uses)
*** Correspondence to actual ML encoding (for devs)
** Typing
** Universe Polymorphism
** SProp
** CoInductives
** Native Integers
** VM and native compute
** Module system
** Libraries (dev view)
** Extraction

* Gallina and elaboration, related vernacular commands
** Summary/highlights
** Syntax
** Terms with holes
** Unification (*new*)
** Extended pattern-matching
** Notations
** Implicit Arguments
** Coercions
** Type Classes
** Canonical Structures
** Module System
** Library managment (user view: scoping of defs etc...)
** Other commands

* Proof Languages
** Summary/highlights
** Interactive model, proof handling
*** Parallel proof processing
** Tactics
** Ltac/Ltac2
*** Examples should be integrated there
** ssr
** Other proof languages? At least mention Mtac2!
** Decision procedures
*** Omega/Micromega
*** Ring
*** Nsatz
*** Generalized rewriting

* Developing
** Structuring projects
*** Library managment (user view: examples)
** Coq commands
** coqdoc
** coq_makefile, making plugins
** IDEs: coqide, proof-general, ...

Requirements:
- Good linking/crossref support with coqdoc and other generated files
