## What changed

Proved `AlgebraicGeometry.Scheme.ProjectionRestriction.localData_exists` by assembling two
strictly smaller packages. Added `Sheaf.Paper.RingedProjectionLocalBaseData` for localized
restriction, operation, tensor, and shift fields, and
`Sheaf.Paper.RingedProjectionLocalDerivedData` for the direct-image, K-injective,
pullback-mate, and counit fields. The target imports the derived package proof-only.

## Proved and sorry left

The target hole in `localData_exists` is closed. Two strictly smaller construction theorems
remain split with `sorry`: `localBaseData_exists` (node
`lem-weil-pbc-ringed-projection-local-base-data`) and `localDerivedData_exists` (node
`lem-weil-pbc-ringed-projection-local-derived-data`). No definition contains `sorry`.

## No longer needed

No imports were removed. The target no longer lists the six monolithic proof dependencies
directly; they remain attached to the two split nodes whose proofs will use them:
`lem-weil-pbc-localize-ringed-site-morphism`,
`lem-pur-site-restriction-module-adjunction-exact`,
`lem-weil-pbc-ringed-derived-slice-localization`,
`lem-weil-pbc-ringed-slice-pullback-mate-normalization`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, and
`lem-weil-pbc-ringed-slice-comparisons-shift`. No library module is pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG treated the complete `Local` record as one construction step although its
restriction/tensor and derived-comparison fields are independent packages. The target proof
is now a real constructor assembly from those two smaller statements; the target statement
and the unit route are unchanged.

## New nodes

`lem-weil-pbc-ringed-projection-local-base-data` records the restriction and tensor package
and is stated in `lean/Sheaf/Paper/RingedProjectionLocalBaseData.lean`.

`lem-weil-pbc-ringed-projection-local-derived-data` records the normalized derived comparison
package relative to a base package and is stated in
`lean/Sheaf/Paper/RingedProjectionLocalDerivedData.lean`.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
