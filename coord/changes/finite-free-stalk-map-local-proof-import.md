# exists_local_free_stalk_map

## Reason

The proof requires the positive-rank finite matrix extension theorem as a proof-only import.

## Old

The item module imported only `Sheaf.AlgebraicGeometry.StalkRestrictionComplexIso`.

## New

The item module additionally imports `Sheaf.AlgebraicGeometry.FiniteFreeStalkMapPositive` without `public`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteFreeStalkDegreewiseLocal | N3 | sees no new public declarations; proof-only import |

## Status

landed 20261013T010610-L-2669068 2026-10-13 (merge of deliver/A2/Sheaf.AlgebraicGeometry.FiniteFreeStalkMapLocal)
