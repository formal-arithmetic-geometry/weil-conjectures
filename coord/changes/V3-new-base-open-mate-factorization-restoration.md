# AlgebraicGeometry.newBase_open_mate_factorization

## Reason

Restore the quarantined module assigned in coord/rework.tsv. The 2026-10-20
upstream sync moved the derived-pullback interface into WeilConjectures. The
archived item still privately imports Sheaf.AlgebraicGeometry.DerivedPullbackComposition,
which is now an empty withdrawn module. Its composition theorem is provided by
the upstream module named by the existing dependency node.

## Old

The archived module's private proof import:

```lean
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
```

## New

```lean
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
```

The full theorem, its proof body, all public imports and local options are
preserved verbatim. Only a redundant blank line is also removed. No definition
or statement changes, and no adopted source-library file changes.

## Users

`tools/downstream.py` with `--allow-missing --uses newBase_open_mate_factorization`
reports zero live downstream modules. A source search including quarantine finds
the following archived caller. Its restoration is a separate assigned rework;
no forced adaptation is needed because this repair preserves the interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NewBaseOpenMateFactorization | V3 | Restored from its quarantine archive with the current proof dependency import. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | quarantined; not adapted | The call at archived line 176 has the same arguments and result. The theorem signature and public imports are unchanged. |

The DAG attachment and both existing proof dependencies are retained. The
quarantine archive is preserved. No target statement or unit route changes.

## Status

landed 20261020T174913-L-818695 2026-10-20 (merge of deliver/V3/Sheaf.AlgebraicGeometry.NewBaseOpenMateFactorization)
