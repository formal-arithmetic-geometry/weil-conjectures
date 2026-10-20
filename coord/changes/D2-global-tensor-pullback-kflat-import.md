# AlgebraicGeometry.Scheme.Modules.globalTensorPullback_kflat

## Reason

Restore the assigned quarantined module after the upstream synchronization.
The rework entry records a collision between the Sheaf and upstream providers
of `CochainComplex.tensorPullbackDifferential`. The Sheaf provider is now retired,
as recorded in `retire-kflat-pullback-20261020.md`. The upstream inverse-image
comparison imports the official provider, so this module must select it too.
The existing complete proof compiles with that provider. No theorem signature,
proof term, definition, docstring or target statement changes.

## Old

The quarantined module has this public import:

```lean
public import Sheaf.Algebra.Homology.KFlatPullback
```

The live module path is absent because it was quarantined; the complete archived
file, rather than an empty replacement, is the restoration source.

## New

```lean
public import WeilConjectures.Algebra.Homology.KFlatPullback
```

All remaining imports are retained. The upstream `IsKFlatTensor` and earlier
`IsAcyclicTensorKFlat` definitions have identical bodies; the existing proof
therefore applies the official preservation theorem without a bridge or hole.
One existing proof-local signature is wrapped to satisfy the 100-character
line limit. No DAG change is required: its Lean attachment, dependencies and
proof steps still describe exactly this theorem and proof.

## Users

`tools/downstream.py Sheaf.Paper.GlobalTensorPullbackKFlat --allow-missing
--uses globalTensorPullback_kflat` reports no live downstream modules. A search
of both `lean/` and `quarantine/` finds the following archived consumer, whose
usage was read against the preserved theorem signature.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.GlobalTensorPullbackKFlat | D2 | Restore archive; replace retired public import; wrap one existing proof-local signature. |
| Sheaf.Paper.GlobalTensorPullbackDerivedData | unclaimed, quarantined | Its application at archived line 153 retains the identical theorem interface; no forced adaptation. |

The parent archive and its DAG attachment remain intact. No quarantined module
is withdrawn. The unchanged signature means no downstream statement changes and
no target statement review is reopened by this repair.

## Status

landed 20261020T154043-L-3034685 2026-10-20 (merge of deliver/D2/Sheaf.Paper.GlobalTensorPullbackKFlat)
