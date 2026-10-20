# FiniteFreeResidueModelPullback imports

## Reason

The quarantined module imported the withdrawn duplicate `Sheaf.AlgebraicGeometry.DerivedPullback`,
which conflicts with the adopted upstream declaration of `AlgebraicGeometry.derivedPullback`.
The module must import the adopted upstream source module directly so the proof elaborates in the
current library.

## Old

`public import Sheaf.AlgebraicGeometry.DerivedPullback`

## New

`public import WeilConjectures.AlgebraicGeometry.DerivedPullback`

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel | unclaimed | Its private proof import resolves the same public declarations; no signature change. |

## Status

landed 20261020T211616-L-3477895 2026-10-20 (merge of deliver/A3/Sheaf.AlgebraicGeometry.FiniteFreeResidueModelPullback)
