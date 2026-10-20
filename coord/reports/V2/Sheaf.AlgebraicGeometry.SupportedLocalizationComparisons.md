## What changed

Proved all 21 theorem holes in `Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons`.
Existing theorem signatures, definitions, and canonical comparison maps are unchanged.
Three proved private helpers compute complements of product supports, intersections,
and identity immersions. Mathlib pullback-range formulas replace affine-chart arguments;
`IsOpenImmersion.isoOfRangeEq` constructs both unique open-product identifications.
The existing DAG node now records this proof route.

## Proved and sorry left

Closed 21 holes, all in namespace `AlgebraicGeometry.Etale` and attached to
`def-pur-supported-localization-comparisons`:

- `supportedExternalProduct_eq`
- `supportedFirstOpenMap_fst`
- `supportedFirstOpenMap_snd`
- `supportedFirstOpenMap_open`
- `supportedFirstOpenSupport_complement`
- `exists_unique_supportedFirstProductComplementIso`
- `supportedFirstProductComplementIso_over`
- `supportedFirstProductComplement_support`
- `supportedFirstIntersection_complement`
- `supportedSecondOpenMap_fst`
- `supportedSecondOpenMap_snd`
- `supportedSecondOpenMap_open`
- `supportedSecondOpenSupport_complement`
- `exists_unique_supportedSecondProductComplementIso`
- `supportedSecondProductComplementIso_over`
- `supportedSecondProductComplement_support`
- `supportedSecondIntersection_complement`
- `supportCutOpenMap_over`
- `supportCutOpenMap_open`
- `supportRestrictedIntersection_complement`
- `supportRestrictedCut_complement`

Holes added: zero. Holes left in the item module: zero. No split-off statements.
The proofs reuse the existing `supportOnOpen_complement` theorem; its upstream
hole, and other pre-existing dependency holes, are unchanged.

## No longer needed

Removed the redundant direct public imports
`Sheaf.AlgebraicGeometry.SupportedExteriorProduct` and
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`.
Both remain publicly available through `NormalizedSupportTriangle`'s existing import
closure, so importer visibility is unchanged. No entire module or DAG node is pruned.
No affine-chart or support-ideal calculation is needed: Mathlib's general
`Scheme.Pullback.range_map` and `Scheme.Pullback.range_fst_comp` suffice.

## Where the brief, the DAG or earlier work was wrong

The node had no proof steps despite the module containing 21 theorem holes.
Added the proof steps actually checked in Lean. No false statement, definition repair,
or unit-route departure was found. The empty-support and full-support cases are
covered by the same set-complement formulas, including the explicit identity-immersion
complement calculation. No new nodes or forced adaptations.

Public-import change record: `coord/changes/V2-supported-localization-redundant-imports.md`.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
