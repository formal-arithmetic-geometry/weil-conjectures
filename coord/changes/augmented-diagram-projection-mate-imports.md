# CategoryTheory.StrictReduction.augmentedDiagramProjectionMate

## Reason

Remove a redundant public import of RingedToposMorphism. It remains publicly imported
by RingedConstantTowerPushforwardNormalization, which this module still publicly imports.
The public import closure, declaration signatures and definition bodies do not change.
Private proof imports of ProjectionMateExact, DiagramSiteRealization,
SmallModuleDiagramsGrothendieck and Mathlib.CategoryTheory.Abelian.FunctorCategory are
also unnecessary for the direct adjunction proof and are removed.

## Old

```lean
public import Sheaf.Paper.ReductionPullbackDerivedTower
public import Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Mathlib.CategoryTheory.Abelian.FunctorCategory
```

## New

```lean
public import Sheaf.Paper.ReductionPullbackDerivedTower
public import Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AugmentedDiagramProjectionMate | S3 | Proof completed; redundant imports removed. |

The source search finds no current Lean importer of the item. Its DAG parents remain
valid and the node and its Lean attachment are retained. Future importers see exactly
the same public import closure, so no forced adaptation or target statement review is needed.

## Status

landed 20261021T130139-L-2562071 2026-10-21 (merge of deliver/S3/Sheaf.Paper.AugmentedDiagramProjectionMate)
