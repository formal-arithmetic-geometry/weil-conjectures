# AlgebraicGeometry.residue_ne_zero_rankOne_stalk_coefficient

## Reason

Restore the complete quarantined module named by its current rework row. The
2026-10-20 cluster restore reverted the module; the archive still imports the
withdrawn Sheaf derived-pullback module. Import the canonical adopted upstream
module directly, as the restored ResidueStalkHomologyMapComparison already does.
This restores the full theorem and its two proved private helpers, rather than
withdrawing its Lean attachment or replacing the archive with an empty module.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

All declaration signatures, visibility, docstrings and proof bodies are preserved
verbatim from quarantine. The existing canonical `AlgebraicGeometry.derivedPullback`
is the same declaration used by the restored comparison theorem. No definition or
mathematical statement changes and no target requires statement re-review.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ResidueHomologyRankOneCoefficient | K4 | Restored from quarantine with the canonical public import; server compile passes. |
| Sheaf.AlgebraicGeometry.RankOneResidueStalkComponent | unclaimed/quarantined | The direct importer and sole external named consumer passes the same arguments at its existing application; the restored theorem type is unchanged. |

`tools/downstream.py ... --uses residue_ne_zero_rankOne_stalk_coefficient` reports
unknown module because the item is quarantined and absent from the live library.
A source search of both `lean/` and `quarantine/Sheaf/` finds the archived parent
above as the sole importer and external named consumer. Its proof application and
the matching parent DAG proof dependency were checked. No consumer adaptation is
necessary. The parent has not been withdrawn and its dependency is retained.

## Status

landed 20261020T221235-L-4162762 2026-10-20 (merge of deliver/K4/Sheaf.AlgebraicGeometry.ResidueHomologyRankOneCoefficient)
