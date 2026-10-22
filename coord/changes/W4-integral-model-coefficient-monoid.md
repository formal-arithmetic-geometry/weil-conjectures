# WeilConjectures.SixFunctors.integralModel_coefficientMonObj

## Reason

Avoid repeated normalization through the bundled `mapMon` construction when elaborating
pulled-back internal module categories. Construct the same monoid object directly with
`Functor.monObjObj`. In server compilations of the same twenty proved reduction helpers,
the original implementation took 49.4 seconds and this implementation took 37.6 seconds.
The diagnostic also proved equality of the old and new values by `rfl`, universally in
both original parameters and their original monoid instance. This changes neither the
monoid operations nor any mathematical statement. The signature, visibility, and
instance attributes remain verbatim. There are no new data or assumptions.

## Old

```lean
noncomputable instance integralModel_coefficientMonObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) : MonObj (condensedRingObj Λ X) :=
  (coefficientRing X (Mon.mk Λ)).mon
```

## New

```lean
noncomputable instance integralModel_coefficientMonObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) : MonObj (condensedRingObj Λ X) :=
  Functor.monObjObj (F := upperStarFromPoint X) Λ
```

## Users

`tools/downstream.py Sheaf.SixFunctors.IntegralModelsGenerators --uses
integralModel_coefficientMonObj` reports 64 downstream modules in the final shared snapshot.
The only textual use is the defining instance. Implicit users receive the identical
instance value by the compiled universal `rfl` check.
No module needs adaptation. No Challenge target changes. Each row below is checked
by substituting the definitionally identical value; its statement and proof stay unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralModelsGenerators | W4 | Equal implementation; unchanged signatures. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Definitionally identical; no adaptation. |

## Status

landed 20261022T025343-L-1291361 2026-10-22 (merge of deliver/W4/Sheaf.SixFunctors.IntegralModelsGenerators)
