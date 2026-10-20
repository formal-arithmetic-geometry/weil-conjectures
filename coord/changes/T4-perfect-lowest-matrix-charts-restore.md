# AlgebraicGeometry.Scheme.exists_perfectLowestMatrixCharts

## Reason

Restore the quarantined local matrix-chart theorem after the upstream sync.
Its old proof-only composition import pulled the retired duplicate derived
pullback into the canonical source environment. Use the canonical source
composition theorem instead. There is no definition or statement change.

## Old

The relevant archived proof imports, verbatim:

```lean
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
```

## New

```lean
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
```

All public imports, the declaration signature and its complete proof are retained
verbatim. The unused flat-complex import is removed.

## Users

The item is absent from the live Lean tree, so tools/downstream.py reports it as
unknown. Searched the live Lean tree, the quarantined direct consumer, and DAG
citations. The consumer below still uses exactly the retained signature. There
are no live direct importers and no adapted consumer modules. All transitive
users receive the same theorem and definitions when their quarantine is repaired.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectLowestMatrixCharts | T4 | Restored complete theorem; signature unchanged. |
| Sheaf.AlgebraicGeometry.PerfectLowestMatrixClosedLocus | unclaimed, quarantined | Same chart theorem and signature; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineFreeLowestMatrixLocus | unclaimed | Byte-identical source recompiled for validation; no change. |

## Status

landed 20261020T174856-L-813722 2026-10-20 (merge of deliver/T4/Sheaf.AlgebraicGeometry.PerfectLowestMatrixCharts)
