# StrictTowerAdjunctionRealization proof imports

## Reason

The public DiagramSiteRealization import was unused by the statement and the completed
proof. Its same-universe existence API is replaced by a private explicit module-equivalence
construction using the vertical topology. Removing it prunes an unused proof dependency.
All other removed imports were already private proof imports.

## Old

```lean
public import Sheaf.CategoryTheory.DiagramSiteRealization
```

## New

The public import is removed. The construction uses the private proof import:

```lean
import Sheaf.CategoryTheory.DiagramSiteTopology
```

No existing signature, definition body, instance, attribute or docstring changes.
Only the body of towerAdjunctionRealization is filled, with proved private helpers added.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictTowerAdjunctionRealization | W3 | Completed proof; unused import removed. |
| Sheaf.AlgebraicGeometry.ProperOpenAlphaPasting | unmodified consumer | No use of exists_diagramSite_realization; signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenClopenProjector | unmodified consumer | No use of exists_diagramSite_realization; signatures unchanged. |
| Sheaf.AlgebraicGeometry.StrictTowerOrdinaryProperOpenArrows | unmodified consumer | No use of exists_diagramSite_realization; signatures unchanged. |
| Sheaf.AlgebraicGeometry.TowerMateEvaluationScalars | unmodified consumer | No use of exists_diagramSite_realization; signatures unchanged. |

`tools/downstream.py Sheaf.AlgebraicGeometry.StrictTowerAdjunctionRealization
--uses exists_diagramSite_realization` reports these four downstream modules and zero
textual users of that declaration. The import-pruning checker passes.
No module held by another group is changed. No target statement or definition changes.

## Status

landed 20261023T152122-L-451592 2026-10-23 (merge of deliver/W3/Sheaf.AlgebraicGeometry.StrictTowerAdjunctionRealization)
