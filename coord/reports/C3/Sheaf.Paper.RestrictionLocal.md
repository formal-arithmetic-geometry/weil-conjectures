## What changed

Completed `AlgebraicGeometry.ProEtale.restrictionLocal` with its exact original signature.
The proof constructs the two derived pullback lifts, compares composite adjunctions using
localizing lower-shriek composition, and obtains the displayed natural isomorphism by
right-adjoint uniqueness. For bounded constructibility it uses affine-space rational purity,
closed-adjoint normalization and rational closed-support preservation. Proved private helpers
transport localizing closures and adjunctions along coefficient
isomorphisms, and use the existing `shriekCoefficientCompactificationIso` for compactification
functors. Reused `shriekCoefficientIso_transport` and its proved inverse-transport
isomorphism rather than rebuilding those equivalences, so the theorem applies to every coefficient ring in its stated isomorphism class.
The finite-cover clause reindexes the already proved affine-chart theorem by `Fin`.
The complete proof compiled through `lcompile.py` in 41.9 seconds after restricting
type transparency in private helpers and the proof body; its unchanged public signature
retains the original settings. The first delivery preflight timed out at 60 seconds before
this optimization. Retained statement binder names caused unused-name warnings; the final
source scopes that linter off at this theorem, preserving its exact signature.

Added only private proof imports and proved private helpers; retained all original public
imports and the theorem signature. Updated the existing DAG node to record the implementation.
The lexical proof settings are documented in
`coord/changes/C3-restriction-local-proof-context.md`.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.ProEtale.restrictionLocal`
(node `det-thm-restriction-local`). Added zero holes; split off zero statements.
No `sorry` remains in the item or in any other delivered file. Existing imported theorem
holes, in particular `affineSpace_rational_induction`, remain with their existing owners;
this delivery proves the item from those stated dependencies as required by stage 3.

## No longer needed

Removed direct proof imports `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
and `Sheaf.Paper.ClosedSupportConstructible`. The proof uses the exact-functor comparison
already available from the derived functor API, and the finite-constant-model support result
rather than the weaker locally-finitely-presented support statement. Removed corresponding
direct proof dependencies `sk-def-sfb-derived-categories` and
`det-prop-closed-adjoint-constructible-support`. The existence theorem
`sk-prop-sf-existence` is no longer a proof dependency: the right adjoints and their
adjunctions are inputs to this theorem. Its statement dependency and public import stay.
The direct dependencies `lem-weil-pbc-quasi-separated-affine-cover-criterion` and
`lem-weil-pbc-qcqs-finite-affine-open-cover` are replaced by the existing proved
`lem-sf-affine-chart-factorization-gluing`, which supplies the finite affine charts and
closed factorizations together. Their mathematics is retained in that theorem.
No module is withdrawn, and no claim is made that these dependencies disappear from every
other target route. The unit's affine factorization, purity and closed-support route is kept.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned argument needs explicit transport because the
coefficient hypothesis allows arbitrary isomorphic presentations, while affine-space purity
is stated for canonical coefficient rings. The proved private equivalence helpers supply this
glue, without choosing unspecified mathematical data from an existence theorem. Empty charts,
empty schemes and dimension zero use the existing finite-chart and purity statements unchanged.
The rework row records an older quarantine, but the current shared source already contains the
restored item; this delivery preserves that attachment and proves its existing declaration.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
