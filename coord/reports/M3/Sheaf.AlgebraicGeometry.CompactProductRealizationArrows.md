## What changed

Proved `AlgebraicGeometry.Etale.compactProductGlobalSiteMap_isIso` in
`Sheaf.AlgebraicGeometry.CompactProductRealizationArrows`. Install the existing
finite global comparison isomorphism theorem locally, unfold the two specified
comparison composites, and use the standard isomorphism instances for functor
images, natural-isomorphism components, and composition. This follows the existing
docstring proof without changing any statement, definition, or import.

Validation: the item compiles through `lcompile.py`; the delivery preflight checks
the declarations and their axioms.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.compactProductGlobalSiteMap_isIso`
(node `def-pur-compact-product-realization-arrows`).
Added 0 holes; 0 holes remain in the delivered module. No results split off.
The proof uses the already proved
`AlgebraicGeometry.ProEtale.isIso_finiteComparisonGlobalSections`.

## No longer needed

None. No imports, nodes, or modules are removed. The construction and the unit
route remain exactly as recorded; no additional dependency is needed.

## Where the brief, the DAG or earlier work was wrong

None. The existing docstring already describes the complete categorical proof.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
