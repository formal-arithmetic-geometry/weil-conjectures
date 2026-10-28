# WeilConjectures.IntegralHom.IsSignedHomTensor

## Reason
The predicate was moved to the split coordinate module so the item theorem can import the
strictly simpler existence and uniqueness statements without an import cycle.

## Old
`IsSignedHomTensor` was declared in `Sheaf.Algebra.Homology.TwoTermFreeHomTensorComponents`.

## New
`IsSignedHomTensor` is declared in `Sheaf.Algebra.Homology.TwoTermFreeHomTensorCoordinateMap`
with the identical signature.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralHomComparisonRepresentative | unclaimed | public predicate import now comes from coordinate module |
| Sheaf.Algebra.Homology.TwoTermFreeHomTensorComponents | P5 | imports coordinate module |

## Status
landed 20261028T020624-L-2530447 2026-10-28 (merge of deliver/P5/Sheaf.Algebra.Homology.TwoTermFreeHomTensorComponents)
