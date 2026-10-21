# Change record: ZeroBottomArrowPullbackLocal

## Reason

The quarantined module publicly imported a withdrawn empty module, so its public theorem
signature could not expose `Scheme` and `HasDerivedCategory` to downstream importers.

## Old

`public import Sheaf.AlgebraicGeometry.DerivedPullback`

## New

`public import WeilConjectures.AlgebraicGeometry.DerivedPullback`

## Users

The theorem declaration and all argument types are unchanged. Downstream users receive the
adopted source derived-pullback API. Existing consumers need no adaptation.

## Status

landed 20261021T001128-L-1374355 2026-10-21 (merge of deliver/M3/Sheaf.AlgebraicGeometry.ZeroBottomArrowPullbackLocal)
