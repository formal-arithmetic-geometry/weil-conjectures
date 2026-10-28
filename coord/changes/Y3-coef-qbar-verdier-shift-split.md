# CoefQbarVerdier shift split

## Reason

The original proof hole bundles finite exactness with common-stage representative
shift descent. The finite exactness witness is already a field of the rational
Verdier datum, so the representative descent is split into a strictly smaller
public theorem used by the item.

## Old

`descended_shift_compatibility` had proof `by sorry`.

## New

`descended_shift_compatibility` chooses the finite shifts from
`RationalVerdier.Datum.exact`, invokes
`descended_shift_core`, and packages the resulting finite exactness and
comparison coherence.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.CoefQbarVerdierExactness | Q2 | Imports the repaired item; public theorem signature is unchanged. |

## Status

landed 20261028T035019-L-3580883 2026-10-28 (merge of deliver/Y3/Sheaf.SixFunctors.CoefQbarVerdierShift)
