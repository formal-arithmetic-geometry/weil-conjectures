## What changed

Continued the proofs in `lean/Sheaf/Paper/CompactSupportStrictScalarMate.lean`,
preserving all existing signatures, definition bodies, and public imports.

The evaluation/restriction comparison uses the existing
`coefficientSequenceRestriction_evaluation` identity, followed by constant scalar
restriction. Identity on abelian sections characterizes its unique isomorphism.

Finite derived balancing is obtained from the specified ordinary balancing.
Its target restriction is conservative and exact, so the ordinary balancing and
exactness of constant scalar extension imply exactness of finite scalar extension.
The private proof import `import all Sheaf.Paper.FiniteScalarCoordinateData`
reuses its proved exact scalar counit helper. Local irreducibility of existing
localization/adjunction terms prevents expensive implementation unfolding; it
changes no declaration signature or definition.

The existing universal exact scalar counit then identifies the derived scalar
extension with termwise extension. A proved private localization helper constructs
and uniquely characterizes the balancing by its required cochain equation.

## Proved and sorry left

Closed holes (compiler validated in 34.4 seconds):
`WeilConjectures.PurStrictScalar.evaluationRestriction_existsUnique` and
`WeilConjectures.PurStrictScalar.finiteBalancing_existsUnique`.
No holes added; no split-off statements. Of the eight initial holes, two are closed
and six remain, all attached to
`dag/nodes/sec-smooth-purity/lem-pur-compact-support-strict-scalar-mate.json`:

- `WeilConjectures.PurStrictScalar.finiteOrdinaryBalancing_existsUnique`
- `WeilConjectures.PurStrictScalar.factors_isIso`
- `WeilConjectures.PurStrictScalar.pulledBasis_existsUnique`
- `WeilConjectures.PurStrictScalar.proper_biproduct`
- `WeilConjectures.PurStrictScalar.strictProper_biproduct`
- `WeilConjectures.PurStrictScalar.compactSupportStrictScalarMate`

## No longer needed

No existing imports, modules, or nodes withdrawn. Other dependencies remain in the
plan for the remaining original obligations. No global pruning claimed.

## Where the brief, the DAG or earlier work was wrong

The finite derived balancing does not require construction of a quotient basis:
its already stated ordinary balancing and conservative exact restriction give
exactness directly. This preserves the canonical cochain normalization and the
unit route.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
