# Sheaf.Paper.CechCupPullbackCompat public imports

## Reason

The second reading found that Sheaf.AlgebraicGeometry.Coherent is unused by every
signature and proof in this module. All seven theorem signatures remain byte for
byte identical. IsQuasicoherent is already available from the other imports;
no declaration of Coherent is used. A scratch copy omitting the import compiled
without errors or warnings in 35.9 seconds, and all seven axiom lists were checked.

This removes one direct public import. It may remove unrelated names from the
public import closure; it does not change a definition or theorem statement.
`python3 tools/downstream.py Sheaf.Paper.CechCupPullbackCompat` reports zero
modules downstream in the repository snapshot. There is therefore no downstream
user to adapt or target statement whose meaning changes through this edit. The
unit's realized lists are empty and unchanged. No whole-library pruning is claimed.

## Old

```lean
public import Sheaf.Paper.CechComparisonMapNaturality
public import Sheaf.Paper.CechRefinementCochainMap
public import Sheaf.Paper.CechCupProduct
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.EtaleTensorSections
```

## New

```lean
public import Sheaf.Paper.CechComparisonMapNaturality
public import Sheaf.Paper.CechRefinementCochainMap
public import Sheaf.Paper.CechCupProduct
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
public import Sheaf.AlgebraicGeometry.EtaleTensorSections
```

## Users

The read-only downstream script reports zero modules downstream of this item.
No adapted modules are delivered. The table consequently has no user rows.

| module | group holding it | effect |
|---|---|---|

## Status

landed 20261013T060429-L-586224 2026-10-13 (merge of deliver/V3/Sheaf.Paper.CechCupPullbackCompat)
