# exists_isAmple_of_enough_globallyGenerated

## Reason

The upstream sync commented out this theorem because its proof could not resolve the
private `nonvanishingLocus_iso` helper after the helper moved to the upstream module.
The repair imports the upstream `WeilConjectures.AlgebraicGeometry.AmpleIso` with
`import all`, which exposes the existing helper, and restores the theorem proof.

## Old

The theorem was commented out in `Sheaf.AlgebraicGeometry.ExistsAmpleOfEnoughGloballyGenerated`.
The former proof imported `all Sheaf.AlgebraicGeometry.AmpleIso` and failed with
`Unknown identifier nonvanishingLocus_iso`.

## New

The theorem is active with its existing statement and proof, and the proof-only import
is `import all WeilConjectures.AlgebraicGeometry.AmpleIso`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.IntegralDimOneAmple | Q6 | imports and applies the repaired criterion |
| other downstream modules | unclaimed | declaration becomes available; signatures unchanged |

## Status

landed 20261018T062856-L-671370 2026-10-18 (merge of deliver/Q6/Sheaf.AlgebraicGeometry.IntegralDimOneAmple)
