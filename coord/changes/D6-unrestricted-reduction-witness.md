# WeilConjectures.unrestrictedIntegralReductionExistence, WeilConjectures.unrestrictedIntegralReductionFunctor

## Reason

The unrestricted tower reconstructed the same universal scalar-extension witness.
Comparing its maps to the intrinsic scalar-reduction transition repeatedly unfolded
that witness. Reuse the recorded scalar witness and functor. The witness uses the
identical standard localizations; the resulting objects, maps, and transitions are
definitionally unchanged. These are unclaimed Sheaf definitions. No target
statement or source-library declaration changes.

`unrestrictedIntegralComplexFunctor` keeps its original body (reviewer, 2026-10-26):
the delivered rewrite as `(scalarReductionExtension ⋙ scalarReductionRestriction).mapHomologicalComplex`
broke the direct importers `Sheaf.Paper.IntegralOperationsWellDefined` (S4) and
`Sheaf.SixFunctors.CompletedTensorFiniteShift` (type mismatches), and the item does
not need it once the two definitions above reduce to the scalar witness.

## Old

```lean
noncomputable def unrestrictedIntegralReductionExistence (n : ℕ) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)))
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (O := completedIntegralCommRingSheafUnrestricted l E Y)
    (O' := integralCoefficientCommRingSheaf l E Y n)
    (completedIntegralCommRingProjectionUnrestricted l E Y n)

noncomputable def unrestrictedIntegralReductionFunctor (n : ℕ) :
    integralTowerModules l E Y ⥤
      SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n) :=
  (unrestrictedIntegralReductionExistence l E Y n).choose

```

## New

```lean
@[implicit_reducible] noncomputable def unrestrictedIntegralReductionExistence (n : ℕ) :=
  scalarReductionExistence l E Y n

@[implicit_reducible] noncomputable def unrestrictedIntegralReductionFunctor (n : ℕ) :
    integralTowerModules l E Y ⥤
      SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n) :=
  scalarReductionExtension l E Y n

```

## Users

The downstream textual-use check covers both names; each listed use retains
the same object and map by definitional equality. No adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicRoosRealizationReductions | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.AdicScalarFlatReductionModel | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.AugmentedIntegralDescent | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.BalancedFiniteTowerGeneratorComparison | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | Q1 | Definitionally identical functor and maps. |
| Sheaf.Paper.ClopenCompletedOperationTowers | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.ClopenRoosIntegralDescent | C3 | Definitionally identical functor and maps. |
| Sheaf.Paper.CoefficientSequenceRoosModel | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.CompletedPerfectScalarPullback | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.CompletedPrimitiveCounitComparison | R6 | Definitionally identical functor and maps. |
| Sheaf.Paper.CompletedPullbackTensorComparison | J6 | Definitionally identical functor and maps. |
| Sheaf.Paper.CompletedPullbackUniverseTransportData | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.CompletedTensorScalarLinearity | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.ConstantScalarStrictUnit | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.ConstantScalarUnitQuasiIsomorphism | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.ConstantWeilStructure | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.FinitePullbackStrictTowerComparison | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.FinitePullbackStrictTowerData | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.FiniteReductionTowerResolvingModel | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralAmbientOperationModels | K1 | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralCompletedTowerPullbackUniverses | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralDerivedOperationsOnSlices | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralOperationsWellDefined | S4 | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | W6 | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralPrincipalConeQuotientAugmentation | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralPullbackShiftCoordinates | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralReductionTower | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralReductionTowerUnrestricted | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralReductionTowerWellDefined | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralReductionTransitionSemilinear | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralTensorReductionTowerComparison | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IntegralTensorTransitionCompatibility | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IsomorphismComparisonNatural | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IsomorphismReductionTower | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.IsomorphismScalarTensorKFlatModel | H5 | Definitionally identical functor and maps. |
| Sheaf.Paper.NormalizedDVREffectivity | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.NormalizedDVRKFlatReductionModel | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.NormalizedDVRKFlatTransition | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.NormalizedIntegralTensorTower | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.OpenCompletedRestrictionIdentification | T4 | Definitionally identical functor and maps. |
| Sheaf.Paper.PodReindexingCompletedEvaluationReflection | Y6 | Definitionally identical functor and maps. |
| Sheaf.Paper.PointPullbackRepresentativeDiagram | A5 | Definitionally identical functor and maps. |
| Sheaf.Paper.PointQuotientTowerHomotopy | A6 | Definitionally identical functor and maps. |
| Sheaf.Paper.PointTransportConeComparisonDescent | H4 | Definitionally identical functor and maps. |
| Sheaf.Paper.PointTransportStrictQuotient | J1 | Definitionally identical functor and maps. |
| Sheaf.Paper.PrimitiveQuotientRealizationComparisons | S7 | Definitionally identical functor and maps. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.PurSequenceAdjointResolutionData | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.PurSequenceAdjointResolutionShifts | M5 | Definitionally identical functor and maps. |
| Sheaf.Paper.PurSequenceKFlatComparisonShifts | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.PurSequenceProjectionHomNormalization | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.RoosIntrinsicCompletenessEquivalence | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.SfStrictDirectImageScalarComparison | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.StrictDvrFlatTensorSequence | unclaimed | Definitionally identical functor and maps. |
| Sheaf.Paper.TraceBoundedQuotientStalkRealization | K8 | Definitionally identical functor and maps. |
| Sheaf.SixFunctors.CompleteLiftedTopCellTriangle | unclaimed | Definitionally identical functor and maps. |
| Sheaf.SixFunctors.CompletedTensorFiniteShift | unclaimed | Definitionally identical functor and maps. |
| Sheaf.SixFunctors.CompletedTensorShiftRight | unclaimed | Definitionally identical functor and maps. |
| Sheaf.SixFunctors.OpenProjectionCompletedSquare | unclaimed | Definitionally identical functor and maps. |
| Sheaf.SixFunctors.OpenProjectionOrdinaryRoos | unclaimed | Definitionally identical functor and maps. |
| Sheaf.SixFunctors.OpenProjectionRestrictionNormalization | unclaimed | Definitionally identical functor and maps. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | Definitionally identical functor and maps. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletionData | unclaimed | Definitionally identical functor and maps. |
| Sheaf.SixFunctors.OpenTensorAugmentationLimitSquare | unclaimed | Definitionally identical functor and maps. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Definitionally identical functor and maps. |
| Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent | unclaimed | Definitionally identical functor and maps. |
| Sheaf.TraceFormula.IsomorphismRoosUnitCancellation | unclaimed | Definitionally identical functor and maps. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | unclaimed | Definitionally identical functor and maps. |
| Sheaf.TraceFormula.StrictQuotientCompletionUnit | unclaimed | Definitionally identical functor and maps. |
| Sheaf.TraceFormula.StrictQuotientConeAugmentation | unclaimed | Definitionally identical functor and maps. |

## Status

landed 20261025T201631-L-2591332 2026-10-25 (merge of deliver/D6/Sheaf.Paper.ConcreteIntegralProjectionCone)
