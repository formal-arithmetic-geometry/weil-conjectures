## What changed

Filled `AlgebraicGeometry.Etale.compactProductGlobalSiteMap_isIso` in
`Sheaf.AlgebraicGeometry.CompactProductRealizationArrows`. Install the existing
`ProEtale.isIso_finiteComparisonGlobalSections c.Z A` locally, expose the explicit
terminal-evaluation transport in `supportGlobalComparison`, and infer invertibility
of the composite from invertibility of each factor and preservation by functors.
The finite-comparison theorem is already publicly available through
`SupportSiteComparison`, so no additional import is required.

Updated the item's node proof and proof dependencies to record this argument.
All declaration signatures, data definitions, docstrings and public imports are preserved.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.compactProductGlobalSiteMap_isIso`
(node `def-pur-compact-product-realization-arrows`).

Holes added: zero. Holes remaining in the delivered module: zero.
No split-off statements.

## No longer needed

None. No imports, nodes or modules removed. The original node had no proof steps
or proof dependencies to prune. All existing statement dependencies remain.

## Where the brief, the DAG or earlier work was wrong

The definition node had an empty proof plan despite its one invertibility theorem.
Its existing theorem docstring gives the needed proof; the updated node records it.
No mathematical error or statement repair was needed.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
