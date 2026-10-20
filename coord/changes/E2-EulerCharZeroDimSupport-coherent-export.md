# AlgebraicGeometry.Scheme.Modules.eulerChar_zero_dim_support

## Reason

Restore the quarantined module and repair the rework diagnostic: the public theorem
mentions `RingedSpace.IsCoherent`, but its defining module was imported privately.
Promote that import to public and close the theorem's existing proof hole.
The theorem's signature, attributes, and definitions are unchanged.

## Old

```lean
import WeilConjectures.AlgebraicGeometry.Coherent
```

The existing theorem had the identical signature and proof `by sorry` in
`quarantine/Sheaf/AlgebraicGeometry/EulerCharZeroDimSupport.lean`.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.Coherent
```

The complete proof uses the existing finite-support reduction, finite-scheme tensor
calculation, module-cohomology source comparison, and affine-pushforward invariance.
This adds visibility for a declaration already used in the public signature; it
changes no mathematical definition or target type.

## Users

`tools/downstream.py` reports the module as unknown because it is quarantined.
An independent scan of imports under `lean/` and `quarantine/` finds no live users
and the following six archived direct users. Three explicitly public-import
`WeilConjectures.AlgebraicGeometry.Coherent`: SnapperNumericalPolynomial,
NodalNormalizationQuotient, and CurveEulerTensorGenericRank. The other three do not.
The theorem signature is byte-for-byte identical to the archive, and promoting the
coherence import only adds visibility. This delivery therefore forces no consumer
adaptation. All six remain quarantined and are outside the current live library.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperIntegralCurveAmpleDegree | unclaimed | Archived; same signature, no adaptation. |
| Sheaf.AlgebraicGeometry.SnapperNumericalPolynomial | unclaimed | Archived; same signature, no adaptation. |
| Sheaf.AlgebraicGeometry.NodalNormalizationQuotient | unclaimed | Archived; same signature, no adaptation. |
| Sheaf.AlgebraicGeometry.CurveEulerTensorGenericRank | unclaimed | Archived; same signature, no adaptation. |
| Sheaf.TraceFormula.ReducedCurveNormalizationGenus | unclaimed | Archived; same signature, no adaptation. |
| Sheaf.TraceFormula.PointedGenusZeroProjectiveLine | unclaimed | Archived; same signature, no adaptation. |

## Status

landed 20261020T154934-L-3174110 2026-10-20 (merge of deliver/E2/Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport)
