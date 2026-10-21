## What changed

Proved `AlgebraicGeometry.Scheme.proEtale_torInterval_local_detection` with its original
signature and public imports. The two clauses share a proved comparison identifying
pullback of tensor cohomology with tensor cohomology of the pulled-back inputs.
The specified independent-coefficient tensor is given the existing pro-etale tensor
model by whiskering its resolving-class representative comparisons, with explicit
complex/homotopy localization isomorphisms. The cover argument forgets actions using
the proved canonical module-unit comparison, identifies inverse image with localization
restriction, and applies the already proved pro-etale covering conservativity lemma.
The closed/open argument applies the existing module zero-detection theorem.
All added helpers are private and fully constructed or proved; there are no new public declarations or modules.

The command-change record is
`coord/changes/p4-proetale-tor-interval-proof-commands.md`. The consumer search found
zero downstream modules; no consumer adaptation is required.

The DAG copy records these comparisons and the shorter exact-functor route. The generic
Kan-extension theorem is unnecessary because the specified derived pullback is already
Mathlib's exact termwise descent. The existing canonical module-unit node is used as a
general tool to identify the underlying abelian inverse image; it imposes no hypotheses
on the scheme, coefficient ring, or module.

## Proved and sorry left

Closed the one assigned hole:
`AlgebraicGeometry.Scheme.proEtale_torInterval_local_detection`
(`lem-sfb-tor-interval-local-detection`). Zero holes remain in the item, and zero holes
are added or split off. This is a proof from existing declarations, including the existing
`proEtaleCanonicalTensorPullback` theorem for canonical tensor pullback; its own proof is
outside this delivery. No claims of axiom-freeness of that dependency are made.

The cover proof preserves the explicit quasi-compact-cover hypothesis when constructing
the pro-etale precoverage cover. The argument also covers zero coefficient rings and empty
schemes/covers: it uses only zero-object detection and the existing covering-sieve theorem,
with no nonempty-index or nonzero-ring assumption. The interval and all universe binders
are unchanged. Final server compilation passed (53.8 seconds); every proof import passed
the import-cycle check, and the statement and public imports were checked verbatim
against the assigned source.

## No longer needed

Removed the direct proof imports:

- `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`;
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`;
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` (the existing pro-etale
  specialization supplies the required comparison);
- `Mathlib.CategoryTheory.Sites.LocalProperties` (the already proved pro-etale
  specialization supplies cover-local detection).

The proof no longer directly needs nodes `lem-trf-geometric-inverse-image-exact`,
`lem-weil-pbc-exact-functor-derived-factorization`, or
`lem-weil-pbc-exact-functor-derived-functor`; they are removed from this node's proof
dependencies and the obsolete top-level `tool_uses` entries. Exactness and termwise descent are already part of the specified
pro-etale operations. The complex-cohomology and cover-local criterion nodes remain,
through their proved source-library derived/pro-etale specializations. No library module
is withdrawn, and no adopted source declaration or public import is changed.

## Where the brief, the DAG or earlier work was wrong

No statement or source error was found. The original plan can be implemented using
existing specialized interfaces, without introducing a separate derived-functor
comparison. The tensor presentation must explicitly insert `quotientCompQhIso`:
localization of complexes and quotient followed by localization of the homotopy category
are related by a natural isomorphism, so forcing their definitions to unfold is unnecessary.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
