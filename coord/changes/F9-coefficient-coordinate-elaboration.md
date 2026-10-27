# AlgebraicGeometry.ProEtale.SpTowerP1 coefficient-coordinate elaboration

## Reason

The refreshed delivery compile timed out in TowerP1CoefficientCoordinates.
A focused profiler compile passed in 31.6 seconds but reported 22.8 seconds
of kernel type checking, including three large checks of 9.07, 6.38 and 5.94
seconds, versus only 1.06 seconds of elaboration. Keep the recorded realization
and derived functor folded while elaborating the existing isomorphism formulas.
This is a local elaboration change, not a different construction or a raised limit.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

All declaration signatures, fields, attributes and defining expressions are retained.

## New

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] AlgebraicGeometry.ProEtale.SpTowerP1.realization
  CategoryTheory.Functor.mapDerivedCategory
```

TowerP1CoefficientCoordinates has no current module claim in the local snapshot.
The local irreducibility controls are placed after CoefficientCoordinates,
so the ordinary section formulas retain the realization unfolding they need.
The local reducibility controls are not exported. No object, normalization equation,
functor or public signature changes. Development profiling options are removed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.TowerUniformEtaleDomains` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1GeometricCoordinates` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1EtaleFiniteData` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1TensorChainCoordinates` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1EtaleWords` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1PushCoordinates` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerP1Adjunction` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1UniformCtfDomains` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1KernelScalarNormalization` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1EtaleOriginComparisons` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1FormulaLevelComparisons` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1TriangleFactorization` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1TensorCoordinates` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurityConjugatesTowerReduction` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1CoefficientCoordinates` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateRightComparisons` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1EtaleDelta` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1FixedTotalTensor` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerTensorAdjointDomains` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1LevelCtfModel` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1ComparisonsWithLine` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1CtfData` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1ProperCtf` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1EtaleEpsilon` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerDomain` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateFoundations` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGluingData` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGamma` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1LevelWords` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1EtaleOperations` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateCategories` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1ProjectiveCoordinates` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1SingleLevelTriangles` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1ProjectionLevelComparisons` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeEvaluation` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1TensorOrdinaryCoordinates` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerP1OrdinaryPushCoordinates` | unclaimed in local claim snapshot; unchanged except named dependency | Identical public declarations and definitions; no adaptation. |

## Status

landed 20261025T202024-L-2664705 2026-10-25 (merge of deliver/F9/Sheaf.Paper.SmoothPurityTowerP1Adjunction)
