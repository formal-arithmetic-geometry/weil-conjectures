## What changed

Restored the live SHEAF declarations and interfaces from before the returned retirement
attempt: `StrictHenselizationRestriction`, `StrictHenselizationClosedLift`,
`StrictLocalNeighbourhoodGeometry`, C3's `StrictLocalMateContinuityPresentation`,
and the original direct consumers. Their public statements and imports are unchanged.
Removed the duplicate `StrictHenselizationRestrictionCompat` module and its split DAG
node; it was a renamed copy of the upstream restriction and was not a valid separate
interface. The compatibility module is listed in `deleted.txt`.

The item remains unretired because the live consumers still use the SHEAF
strict-henselization API. Converting or retiring those consumers requires a separate
bottom-up migration to the upstream `strictLocalization` API, and the returned review
identified that migration as a blocker for this item.

## Proved and sorry left

No theorem proofs were changed and no new declarations were added. The restored item
has the two previously proved declarations
`existsUnique_strictHenselizationStalkRestriction` and
`strictHenselization_globalSections_preservesFiniteColimits`; both remain sorry-free.
No `sorry` is added or left by this delivery.

## No longer needed

The duplicate module `lean/Sheaf/AlgebraicGeometry/StrictHenselizationRestrictionCompat.lean`
and node `def-weil-pbc-strict-henselization-restriction-compat` are withdrawn. No live
consumer import is redirected to the duplicate module. The upstream twin is not used
to replace the live SHEAF restriction declarations in this delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier retirement packet treated the upstream twin as a byte-compatible replacement.
Its declarations use `strictLocalization` and `strictLocalizationToBase`, while the
live SHEAF consumers use `strictHenselizationScheme` and
`strictHenselizationStructuralMap`. The attempted compatibility copy hid this mismatch
and also introduced duplicate structural-map declarations. The return correctly requires
restoring the live closed-lift and neighbourhood-geometry interfaces and deleting the
compatibility copy. A complete retirement is blocked until the dependent consumers are
migrated or retired bottom-up; this delivery therefore leaves the item unretired.

## New nodes

None.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
