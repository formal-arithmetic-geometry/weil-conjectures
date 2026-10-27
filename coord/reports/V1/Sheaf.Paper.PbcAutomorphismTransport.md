## What changed

Filled two of the four original theorem holes in
`lean/Sheaf/Paper/PbcAutomorphismTransport.lean`:
`pbcIsoCompletedComparison_isIso` and `pbcIsoIntegralPullback_isEquivalence`.

The completed comparison uses the existing preservation theorem's intrinsic
completeness clause, transports its presentation witness along the ordinary
comparison, and applies canonical completeness and completed pullback as
completion. The preservation theorem is moved before this proof; its signature,
docstring and original hole are unchanged.

The integral equivalence uses ambient fullness and faithfulness and essential
surjectivity furnished by transport along the inverse scheme isomorphism.
Existing derived pullback composition and identity comparisons give its counit.
New proof imports are `Sheaf.Paper.PbcActualRingedExchange` and
`Sheaf.Paper.SfConstructibleCanonicalCompleteness`, both private.
The node proof plan records these arguments. Public signatures and definitions
are unchanged.

## Proved and sorry left

Holes closed (2 of 4 original holes):

- `AlgebraicGeometry.Scheme.pbcIsoCompletedComparison_isIso`.
- `AlgebraicGeometry.Scheme.pbcIsoIntegralPullback_isEquivalence`.

Holes left (2), both with node `def-wf-automorphism-completed-transport`:

- `AlgebraicGeometry.Scheme.pbcIsoAmbientPullback_preserves`: transport of
  intrinsic completeness, uniform constructible reductions and compatible
  etale origins. Its original source and proof in words are retained.
- `AlgebraicGeometry.Scheme.pbcIsoAmbientScalarComparison_exists`: normalized
  derived scalar comparison. Its original source and proof in words are retained.

Holes added: zero. No new nodes or axioms. Both closed theorems use the retained
preservation theorem; their transitive axiom closures are not yet sorry-free.

## No longer needed

No original imports, nodes or modules are removed. An attempted scalar proof
using `Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares` typechecked but
exceeded the compile limit, so that proof and its new import are absent from
this delivery. The original scalar hole remains in place; it is not split off.

## Where the brief, the DAG or earlier work was wrong

The DAG grouped the four remaining obligations in one step. The updated plan
separates the two proved consequences from the two original remaining holes.
No unit route is bypassed: this unit's realized statement and steps are empty,
and all public constructions are retained. The scalar proof attempt required
98 seconds; profiling and a proved generic helper did not reduce it below the
required 60 seconds. The delivered source contains no profiling options.

Validation: the complete module compiled successfully through `lcompile.py`
in 52.8 seconds during the scoped profile run. Diagnostic wrappers were removed
for delivery; the delivery tool verifies the final source.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
