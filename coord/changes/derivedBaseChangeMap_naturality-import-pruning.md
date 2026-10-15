# derivedBaseChangeMap_naturality: import pruning

## Reason

The module-coefficient naturality theorem uses only the original unbounded exchange
natural transformation and the chosen Cartesian square type. Import their defining
modules directly. The removed imports supply unrelated ringed-space-module naturality,
the underived square comparison, and set/abelian exchange helpers. No existing
statement, declaration visibility, or definition changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedBaseChangeNaturality
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
```

## New

```lean
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DerivedBaseChangeMapNaturality --uses
derivedBaseChangeMap_naturality` lists the following four downstream modules. It finds
no textual use of the theorem outside its declaring module.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange | A4 | Sole direct importer, by a plain proof import. It independently imports DerivedBaseChangeNaturality and publicly imports BaseChangeMapAbelianAndSets, which publicly imports BaseChangeInverseImageIso. The original source compiles against the revised module; no adaptation. |
| Sheaf.Targets.EtaleSmooth | C1 | Transitive importer through BoundedBelowDerivedSmoothBaseChange; no declaration or definition changes, and the direct importer retains all removed dependencies independently. No adaptation. |
| Sheaf.Targets.EtaleSmoothRing | A2 | Transitive importer through BoundedBelowDerivedSmoothBaseChange; same unchanged declarations and independent dependencies. No adaptation. |
| TargetsCheck | unclaimed | Transitive target aggregation; target types and definitions are unchanged. No adaptation. |

No module held by another group is edited. No target statement or target-used
definition changes, so target statement review is not reopened.

## Status

landed 20261015T154154-L-159201 2026-10-15 (merge of deliver/C1/Sheaf.AlgebraicGeometry.DerivedBaseChangeMapNaturality)
