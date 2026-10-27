# AlgebraicGeometry.Etale.FiniteSmoothPurity.scalarSingleMap

## Reason

The chart proof exceeds the 60-second file limit when its coefficient-line normalization
uses the expanded cochain scalar map. Profiling identifies kernel checking of the single
comparison equality (16–36 seconds by itself) and its use in the normalization record
(up to 31 seconds). The canonical adjunction transpose already exists as
`WeilConjectures.PurityFiniteSetting.purityScalarSingleMap`. Use that shared presentation
and prove `scalarSingleMap_cochain`, which recovers the original formula exactly, from
naturality of the exact restriction/single comparison and the cochain adjunction unit.
No hypothesis is added and no map is chosen differently. The compact scalar definition
is elaborated outside the local instance-cache section, so its chosen derived adjoint
uses the same instance arguments as the existing purityScalarSingleMap. The added import is acyclic.
The normalized root-line record and all target meanings stay the same by this equation.
The change is to an unclaimed Sheaf module; no adopted source-tree file is changed.

## Old

```lean
def scalarSingleMap (phi : A →+* B) (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ordinaryScalar phi T).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((ProEtale.etaleSheafExtendScalars phi T).obj M) :=
  (ordinaryScalar phi T).map
      ((_root_.DerivedCategory.singleFunctorIsoCompQ
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).hom.app M) ≫
    scalarExtensionRepresentative phi T ((CochainComplex.singleFunctor _ 0).obj M) ≫
    _root_.DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (ProEtale.etaleSheafExtendScalars phi T) (.up ℤ) 0).hom.app M) ≫
    (_root_.DerivedCategory.singleFunctorIsoCompQ
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) 0).inv.app
        ((ProEtale.etaleSheafExtendScalars phi T).obj M)
```

## New

```lean
def scalarSingleMap (phi : A →+* B) (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ordinaryScalar phi T).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((ProEtale.etaleSheafExtendScalars phi T).obj M) :=
  WeilConjectures.PurityFiniteSetting.purityScalarSingleMap phi T M
```

The public equation `scalarSingleMap_cochain` proves the equality in arbitrary abelian
categories with exact right adjoint. Its specialization to the ordinary scalar adjunction
and its derived adjunction recovers the old right-hand side verbatim. The degree-zero
single/localization identifications are identities, and the cochain-unit formula is
proved by naturality of the exact restriction/single comparison.
All its helpers are proved private theorems. The module still has zero holes.

## Users

`tools/downstream.py Sheaf.Paper.FiniteSmoothCoefficientArrows --uses scalarSingleMap`
lists the following downstream modules. Only the defining module and the two direct
consumers `FiniteTateBalancedScalarPullback` and `FiniteTateScalarSourceNormalization`
mention `scalarSingleMap`; their statements are preserved by the equation above.
No other group's source is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.AdicUnitTraceCounitReductions` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.AdicUnitTraceProjectionAssembly` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.AdicUnitTraceTargetNormalization` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.AdicUnitTraceTensorCoordinates` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.AdicUnitTraceTransposeReductions` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.AffineCounitScalar` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.ChartCounitScalarTransport` | T8 | Proof completed; no signature change |
| `Sheaf.Paper.CondensedTateIntegralTowerData` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.CondensedTateIntegralTower` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.EtaleAffineProjectionCoefficientMate` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteDiagonalOrientationReduction` | U3 | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteDiagonalReductionComparisons` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteOrientationScalarPresentation` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteProductReductionComparisons` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteProductScalarPresentation` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FinitePuritySourceUnitReduction` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteSmoothAdjunctionData` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteSmoothCoefficientArrows` | unclaimed | Equivalent definition and original-formula equation |
| `Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteSmoothLevelOfOrientation` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteSmoothQuotientCoherence` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteSmoothSiteRealizations` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteSmoothTwoLevelReduction` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteSupportedReductionEquation` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteTateBalancedScalarPullback` | H2 | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteTateScalarSourceNormalization` | G3 | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.NormalizedTateTensorTower` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.OrderedTateScalarNormalization` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.P1CounitScalar` | F4 | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.RawChartScalarCounitPasting` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Paper.VectorTraceScalarDescent` | S8 | Same canonical map; no source adaptation needed |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | X2 | Same canonical map; no source adaptation needed |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Same canonical map; no source adaptation needed |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Same canonical map; no source adaptation needed |

## Returned-delivery repair

Removed the inherited warning-suppression option after the landing scanner classified
its dotted name as an unattributed hole. This module has no proof holes and needs no
warning suppression. No declaration, signature, or proof changed in this repair.

## Status

landed 20261025T164404-L-1008539 2026-10-25 (merge of deliver/T8/Sheaf.Paper.ChartCounitScalarTransport)
