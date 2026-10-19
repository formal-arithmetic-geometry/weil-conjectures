## What changed

Filled five proof holes in `Sheaf.AlgebraicGeometry.SupportSiteComparison`:
ordinary support comparison normalization and invertibility, terminal evaluation
normalization, forgetting supports, and the full-support forgetful isomorphism.
The proofs use the existing comparison adjunction, support-kernel comparison,
derived compatibility, and support evaluation APIs. Public declarations and
signatures are unchanged. The private proof helpers and local transparency
options are documented in `coord/changes/SupportSiteComparison-proof-context.md`.
The module compiles successfully.

## Proved and sorry left

Proved:

- `AlgebraicGeometry.ProEtale.supportComparisonUnit_existsUnique`
- `AlgebraicGeometry.ProEtale.supportComparison_isIso`
- `AlgebraicGeometry.ProEtale.supportKernelEvaluationIso_existsUnique`
- `AlgebraicGeometry.ProEtale.supportComparison_forget`
- `AlgebraicGeometry.ProEtale.fullSupportForget_isIso`

The following original holes remain, with their existing source and proof
paragraphs unchanged:

- `AlgebraicGeometry.ProEtale.supportComparison_exterior`
- `AlgebraicGeometry.ProEtale.supportOpenConstantIso_existsUnique`
- `AlgebraicGeometry.ProEtale.supportComparison_open`

No new sorry declarations were added.

## No longer needed

None. No imports, DAG nodes, or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

No statement or definition was changed, and no statement is disputed. The
remaining three declarations require the exterior-product and open-restriction
coherence arguments described by the DAG; the present delivery leaves those
holes in place.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
