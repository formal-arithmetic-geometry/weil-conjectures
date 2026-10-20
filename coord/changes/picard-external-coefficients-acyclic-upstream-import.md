# AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_acyclic

## Reason

The item is quarantined under `coord/rework.tsv`. Its original module is preserved at
`quarantine/Sheaf/AlgebraicGeometry/PicardExternalCoefficientsAcyclic.lean`.
The original public import now refers to an empty withdrawn module. Consequently,
`RingedSpace.moduleCohomology` and `externalCupCoefficients`, both used in the public
statement, are available only through private proof imports. Compiling the restored
original reports unknown-identifier errors for these declarations.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

This is the adopted source module for exactly the same notions. It publicly imports
`WeilConjectures.Topology.RingedSpaceModuleCohomology` and defines the canonical
`externalCupCoefficients`. The replacement is the only Lean source change relative to
the quarantine archive. All declaration signatures, proof bodies, attributes and other
imports stay verbatim. No definition or target meaning changes; no target statement
review is reopened. The restored module compiles without errors or warnings via
`lcompile.py` in 5.2 seconds.

## Users

`tools/downstream.py --uses` reports the item as unknown because its source is
quarantined. Read-only searches of `lean/Sheaf`, `lean/WeilConjectures` and `quarantine` for the
module import and theorem name find exactly the consumer listed below. This repair
preserves the theorem's full original type and provides its public statement
dependencies. It does not force changes to callers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAcyclic | D3 | Restore the quarantined module with its unchanged complete proof. |
| Sheaf.AlgebraicGeometry.PicardExternalCupAcyclic | Quarantined; no adaptation | Its invocation of `picardExternalCupCoefficients_acyclic` has the same name and type. |

The existing DAG attachment, statement, proof dependencies, parent edges and unit route
are retained. The change is a public-import restoration, not a definition repair or a
new proof reduction. No other module is edited and no declaration is withdrawn.

## Status

landed 20261020T160749-L-3403946 2026-10-20 (merge of deliver/D3/Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAcyclic)
