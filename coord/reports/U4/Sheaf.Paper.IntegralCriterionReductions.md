## What changed

Completed `AlgebraicGeometry.ProEtale.integral_reductions_constructible_iff` in
`Sheaf.Paper.IntegralCriterionReductions`, preserving its statement and every existing
public definition. Added proved private helpers for normalized coefficient-module
transport, the successive-reduction triangle, scalar
restriction, and extension closure with a fixed cohomological interval.

The triangle is constructed from the existing flat tensor sequence on a flat-term
K-flat resolution. Completed quotient identifications transport that sequence to the
actual finite coefficient sheaves. Full, faithful exact scalar restriction lifts its
maps and short exactness to the middle quotient. The K-flat counits identify its
derived endpoints with the specified reductions. Simultaneous induction proves
constructibility and the same interval at every positive level; the converse is
level zero (exponent one). Existing normalized finite-model comparisons transport
this result to the continuous presentation.

Added proof-only imports of `StrictDvrFlatTensorSequence`,
`TensorColimitsIndependentCoefficients`,
`SuccessiveQuotientFlatTensorSequence`,
`CompletedCoefficientRegularQuotients`, `ProEtaleFiniteScalarRestrictionConstructible`
and `ProEtaleBoundedConstructibleTriangulated`. Updated the main node's proof,
proof dependencies and proof origin to describe this implementation.
The file-local proof instance settings are documented in
`coord/changes/U4-integral-reductions-proof-context.md`; no consumers need adaptation.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.ProEtale.integral_reductions_constructible_iff`
(node `det-prop-integral-criterion-reductions`).

No holes added or split off. No `sorry` remains in the delivered module.
All new private helpers are proved. The full module compiled cleanly through
`lcompile.py` in 38.5 seconds with no warnings. The pre-existing comparison proofs and final
first-reduction corollaries are retained.

## No longer needed

The abstract `lem-pe-successive-quotient-linear-triangle` is not used directly:
its underlying `lem-pe-successive-quotient-flat-tensor-sequence` construction is
specialized to the actual scalar-extension presentation instead. The regularity
and normalized quotient facts are supplied by
`lem-sp-completed-coefficient-regular-quotients`, so the proof no longer uses
`det-pe-derived-nakayama-resolution` as its coefficient lemma. Removed that node
from the main proof dependencies and its obsolete top-level `tool_uses` approval.
The existing `DerivedNakayamaResolution` import remains necessary for definitions
used in the public signatures. No import was removed, and no module is withdrawn.
These two dependency removals do not assert that other consumers no longer need them.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The DAG's abstract quotient-linear triangle
uses generic quotient presentations, while this module's reductions use fixed
completed projections and chosen derived extension functors. Rather than introduce
new comparison statements, the proof uses the existing flat tensor implementation,
normalized completed quotient isomorphisms, and K-flat counits. This preserves the
blueprint's coefficient exact sequence, distinguished triangle, induction and common
interval argument. Completeness is retained as a hypothesis, although this
all-reductions implication itself does not require it.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
