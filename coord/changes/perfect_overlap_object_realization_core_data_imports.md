# PerfectOverlapObjectRealizationCoreData proof imports

## Reason

The proof of the pointwise comparison theorem uses the existing localization theorem
for exact open restriction and the existing canonical open pullback comparison. These
are proof-only dependencies and are imported without `public`.

## Old

The module imported `PerfectOverlapHomContinuityData`, `PerfectHomTransport`, and
`PerfectOverlapStageEquivalence` only.

## New

The module additionally imports `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionLocalization`
and `Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData` as private proof imports.
The public declarations and all existing signatures remain unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData | K1 | proof uses the two imports |

## Status

landed 20261014T234607-L-1023500 2026-10-14 (merge of deliver/K1/Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData)
