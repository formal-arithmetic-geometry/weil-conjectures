# AlgebraicGeometry.Scheme.Modules.exists_globalTensorPullback_derived_data

## Reason

Restore the assigned quarantined module after the upstream synchronization.
The rework row records that `CochainComplex.tensorPullbackRingMap` is not publicly
available to its theorem signature. The archived public import names the retired,
empty Sheaf twin. Compiling the archive reproduces missing-public-import errors
for that ring map, `TopCat.Sheaf.inverseImageModule`, and
`TopCat.Sheaf.inverseImageModuleMap`.

## Old

```lean
public import Sheaf.Algebra.Homology.KFlatPullback
```

The module is absent from `lean/`; its complete source is preserved at
`quarantine/Sheaf/Paper/GlobalTensorPullbackDerivedData.lean`.

## New

```lean
public import WeilConjectures.Algebra.Homology.KFlatPullback
```

Restore the entire archived file with only this import replacement. The official
upstream module publicly provides the ring map and inverse-image interface used
in the statement. All declarations, theorem signatures, proof bodies, instances,
options, docstrings, and remaining imports are verbatim from the archive. There
are zero proof holes. The corrected file compiles in 28.7 seconds.

## Users

`tools/downstream.py Sheaf.Paper.GlobalTensorPullbackDerivedData --allow-missing
--uses exists_globalTensorPullback_derived_data` finds no live consumers.
An import scan including both library roots and `quarantine/Sheaf` finds 49
transitive consumers and exactly one direct consumer, listed below. Its call
at archived line 186 supplies the same `X e he P hP hm` arguments and consumes
the unchanged derived pair, absoluteness, K-flat computation, and tensor clauses.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.GlobalTensorPullbackDerivedData | C2 | Restore archive with official public import. |
| Sheaf.Paper.ModuleCupGlobalTensorPullback | unclaimed, quarantined | Identical theorem interface and proof application; no forced adaptation. |

All indirect consumers continue through the unchanged parent interface. Their
archives remain intact. No quarantined module is withdrawn, no definition changes,
and no target statement review is reopened. The DAG attachment, proof steps, and
dependencies already describe the restored proof and require no changes.

## Status

landed 20261020T155826-L-3293629 2026-10-20 (merge of deliver/C2/Sheaf.Paper.GlobalTensorPullbackDerivedData)
