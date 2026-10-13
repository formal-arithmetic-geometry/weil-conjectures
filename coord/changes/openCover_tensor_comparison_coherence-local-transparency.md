# AlgebraicGeometry.Scheme.Modules.openCover_tensor_comparison_coherence

## Reason

The new assembly proof must compare large canonical comparison terms without
unfolding their data. The static delivery checker conservatively classifies
an added attribute command as an interface change, even when it is local.
This record documents its actual scope: no exported definition or attribute changes.

## Old

There was no local irreducibility command before the theorem. Its proof was
`:= by sorry`.

## New

```lean
attribute [local irreducible] tensorPullback tensorPullbackCompositionIso
  openCoverTensorPullbackComparison moduleRecoveryComparisonIso pullbackComp pullbackCongr
```

These attributes apply only inside this module. The theorem has the identical
signature and visibility; no construction body or globally visible attribute changes.
The unused-variable linter is disabled only for the unchanged theorem's let binders.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OpenCoverTensorComparisonCoherence | D2 | Proof elaboration only. |
| Sheaf.AlgebraicGeometry.OpenCoverMapLiftTransport | unclaimed | No interface effect; identical theorem type. |

No consumer adaptation is necessary: local irreducibility is not exported.

## Status

landed 20261013T224507-L-1470043 2026-10-13 (merge of deliver/D2/Sheaf.AlgebraicGeometry.OpenCoverTensorComparisonCoherence)
