## What changed

Change record: `coord/changes/X3-retire-determinant-exterior-dual-iso.md`.

Retired the duplicate `Sheaf.AlgebraicGeometry.DeterminantExteriorDualIso` module
(zero textual holes) and attached its DAG node to the complete adopted theorem in
`WeilConjectures.AlgebraicGeometry.DeterminantExteriorDualIso`. The duplicate is
listed in `deleted.txt`.

Adapted the sole direct consumer,
`Sheaf.AlgebraicGeometry.DeterminantDualEvaluation`, to import the adopted theorem
and `Modules.ExteriorSheafPowerComparison`. Its proof transports the upstream
`exteriorPower` isomorphism through the canonical comparisons, preserving the
consumer's original public statement and all hypotheses. The adapted consumer
compiled with `lcompile.py`.

## Proved and sorry left

This is a zero-hole retirement. Closed: 0. Added: 0. Split off: 0. The adopted
upstream theorem is already complete, and the adapted consumer introduces no new
sorry. No declaration in the withdrawn module remains.

## No longer needed

Withdrawn module `lean/Sheaf/AlgebraicGeometry/DeterminantExteriorDualIso.lean` and
its duplicate proof imports. The old Sheaf determinant proof dependencies
`WeilConjectures.AlgebraicGeometry.DeterminantDualPairing` and
`WeilConjectures.AlgebraicGeometry.DeterminantDualPairingLocal` are no longer needed
by the retired module; the canonical comparison remains needed by the adapted
consumer. No upstream module or target route is pruned.

## Where the brief, the DAG or earlier work was wrong

The queue correctly marks this item as `retire`, but the generic worker brief says
to prove every sorry even though the duplicate theorem has zero holes. The adopted
upstream theorem uses the alternate `exteriorPower` representation, so a bare import
replacement would not typecheck. The canonical comparison isomorphisms provide the
necessary transport without changing the consumer's statement or adding hypotheses.

## New nodes

None.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
