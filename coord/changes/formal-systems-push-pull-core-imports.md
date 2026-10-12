# FormalSystemsPushPullCore imports

## Reason

The core proof uses `CoherentFormalModuleAnnihilated`, whose public interface
already exposes the abelian formal-module declarations. The direct public import
of `CoherentFormalModulesAbelian` was therefore removed; proof-only imports remain
private. This is an import visibility change required by pruning.

## Old

```lean
public import Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian
```

## New

The direct import is absent. `CoherentFormalModuleAnnihilated` remains a public
import and supplies the declarations needed by downstream users.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FormalSystemsPushPullCore | Q1 | proof uses the transitive public interface; no declaration signature changes |

| Sheaf.AlgebraicGeometry.FormalSystemsPushPull | unclaimed in the supplied snapshot | sole direct importer; no adaptation, since the same abelian declarations remain available through the retained public import |

## Status

landed 20261012T223412-L-1639275 2026-10-12 (merge of deliver/Q1/Sheaf.AlgebraicGeometry.FormalSystemsPushPullCore)
