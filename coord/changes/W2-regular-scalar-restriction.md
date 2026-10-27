# scalarReductionSource, scalarReductionTarget and scalarReductionRestriction

## Reason

The kernel expands abbreviation heads while checking concrete applications of
restriction to finite coefficient modules. This exposes large completed coefficient
actions before matching the composite functors. Retain the exact category and restriction bodies
as reducible ordinary definitions. Their signatures and all mathematical data are
unchanged by definitional equality. An explicit proved additivity instance exposes
the existing generic structure. The module is unclaimed; no source-library module
is edited and no consumer source adaptations are needed.

The existing proofs now respect transparency. During extraction of the derived
specification, its large witness and ordinary extension are locally irreducible;
ordinary extension is explicitly unfolded for that extraction and its local
semireducibility restored afterward. The proof uses the same witness projection.
Elaboration is sequential. These are proof and checking changes only.

## Old

The category declarations were `noncomputable abbrev`, with the same bodies shown
below. The ordinary restriction and derived-witness extraction were:

```lean
noncomputable abbrev scalarReductionRestriction :
    scalarReductionTarget l E Y n ⥤ scalarReductionSource l E Y :=
  SheafOfModules.restrictScalars
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E Y n))
```

```lean
noncomputable def scalarReductionDerivedExistence :
    ∃ (LF : DerivedCategory (scalarReductionSource l E Y) ⥤
        DerivedCategory (scalarReductionTarget l E Y n))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (scalarReductionExtension l E Y n).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (scalarReductionSource l E Y) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (scalarReductionSource l E Y) ℤ,
          P.IsKFlatIndependentCoefficients →
            IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (scalarReductionExistence l E Y n).choose_spec.choose_spec.choose_spec.choose_spec.2.2
```

## New

```lean
@[reducible]
noncomputable def scalarReductionSource :=
  SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y))
```

```lean
@[reducible]
noncomputable def scalarReductionTarget (n : ℕ) :=
  SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n)
```

```lean
@[reducible]
noncomputable def scalarReductionRestriction :
    scalarReductionTarget l E Y n ⥤ scalarReductionSource l E Y :=
  SheafOfModules.restrictScalars
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E Y n))
```

```lean
instance scalarReductionRestrictionAdditive :
    (scalarReductionRestriction l E Y n).Additive := by
  unfold scalarReductionRestriction
  infer_instance
```

```lean
noncomputable def scalarReductionDerivedExistence :
    ∃ (LF : DerivedCategory (scalarReductionSource l E Y) ⥤
        DerivedCategory (scalarReductionTarget l E Y n))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (scalarReductionExtension l E Y n).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (scalarReductionSource l E Y) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (scalarReductionSource l E Y) ℤ,
          P.IsKFlatIndependentCoefficients →
            IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  unfold scalarReductionExtension
  exact (scalarReductionExistence l E Y n).choose_spec.choose_spec.choose_spec.choose_spec.2.2
```

No object or map wrapper is introduced: all three construction bodies are
verbatim. Definition-sensitive review is requested for every reached target using
these definitions, as required by AGENTS.md section 4. The new additive instance is
attached to the existing scalar-restriction definition node.

## Users

Source scan refreshed 2026-10-26T08:59+00:00.
The import closure has 2097 modules; 217 mention the changed
declarations under the `tools/downstream.py --uses` criterion.
Statements, module actions and constructions remain definitionally equal.
No forced consumer edits are included.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.AdicRoosRealizationReductions` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.AdicScalarFlatReductionModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.AffineCommonProjectiveCharts` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CanonicalOpenRestrictionModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ClopenProjectiveChartCommonRefinement` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | J6 | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientConstantTowerRoos` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientConstantTowerRoosComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientEnrichedGlobalShift` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionFiniteAssociation` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionOrdinaryQuotientIso` | Y2 | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionOrdinaryStrictTensor` | T7 | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionReductionData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionRepresentativeRoos` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionRestrictedTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionStrictRepresentatives` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientReductionNaturalCochainComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientRingedSequenceSite` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientSequenceRoosModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CommonStageLisse` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompactSupportCoefficientTransition` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompactSupportCompleteRestrictionFaithful` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompactSupportInputTowerCompatibility` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompactSupportQuotientCocycle` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompactSupportReductionTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompactSupportReductionTowerConstruction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompactSupportReductionTowerData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompactSupportRepresentativeIndependence` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompleteResidueCohomologyBounds` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompleteTopResidueCellCone` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedCoefficientCompletionRoosTransport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedFreeCellOrdinaryLimit` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedLineComplete` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedOpenTensorRepresentatives` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedPrimitiveCounitComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | E4 | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedPullbackTensorPullbackCounit` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedPullbackTensorTensorCounit` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitCanonicalModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitDerivedAdjunctionComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitFiniteMateComparison` | J9 | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitOrdinaryAdjunction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitRestrictionAcyclicity` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitStrictQuotientModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ConstantCoefficientObjectsConstructible` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ConstantScalarStrictUnit` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ConstantScalarUnitQuasiIsomorphism` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ConstructibleFlatCohomologyTorBound` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ConstructibleProjectiveChartRefinement` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ConstructibleResidueTree` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.DirectImageReductionHomSquare` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.EtaleIntegralLineDerivedComplete` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.EtaleIntegralLineReductions` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ExpressionCounitSubstitutionCoherence` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FieldStageOrdinaryRealization` | F6 | definitionally identical data; no adaptation |
| `Sheaf.Paper.FiniteCoefficientPointStages` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FiniteCounitRestrictionTowers` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FiniteExpressionReductionComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FiniteRestrictionCoefficientCore` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FiniteTorAmplitude` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FlatLineDerivedReduction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FourierAdicArtinSchreier` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | T2 | definitionally identical data; no adaptation |
| `Sheaf.Paper.GeometricStalkPerfect` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralCoefficientCompletenessTransport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralComparisonRealizationModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralCompletedCoefficientTransport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralConstructibleTriangulated` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralCriterionReductions` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralDetailedFiniteReduction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralImmersionPullbackNormalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralImmersionPullbackNormalizationData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralLineChainEvaluations` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralLineDerivedComparisons` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralLineNormalizedDerivedComparisons` | K1 | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralLineNormalizedEvaluations` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralLinePowerComparisons` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralLineReductionDefinitions` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralLineReductionRestriction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralLineRestrictions` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralLineSupportPreservation` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralLineTensorCompleteness` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralMappingLimitProjections` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralOperationRoosEffectivity` | W2 | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralOperationsPreserveConstructible` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralPullbackCounitProjection` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralRationalQbarCompactSupport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralReductionResidueHomology` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralReductionTowerCanonical` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralResidueTor` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralStalkResidueFinite` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralStalkRoosControl` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralStrictReductionModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralTowerInverseImageUnit` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IsomorphismComparisonNatural` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IsomorphismReductionTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.MixedReductionUnit` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedArithmeticInterpolation` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedCompletionRealization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVREffectivity` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRKFlatReductionModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRKFlatTransition` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRRoosAugmentation` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRRoosFiniteReduction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRStrictCoefficientAdjoint` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedTensorConstraintTransport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.OrdinaryQuotientPullbackTowerComparison` | A3 | definitionally identical data; no adaptation |
| `Sheaf.Paper.PodIdentityReductionTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointFibreDerivedTensorBasic` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointFibreDerivedTensorModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointIntegralSectionsConservative` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointReductionUnits` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointRestrictionSystemChainMap` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointSectionsFiniteness` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointSectionsFinitenessIntegral` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointSectionsIntegralCohomologyControl` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointSectionsReconstruction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PrimitiveQuotientPullbackModelExistence` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurCoefficientRoosShiftNormalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurReductionFiniteShiftNormalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurReductionLimitShiftAdjunction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurReductionLimitShiftData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceAdjointResolutionData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceAdjointResolutionShifts` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceComparisonTranspose` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceKFlatComparisonData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceKFlatComparisonShifts` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceProjectionHomNormalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceReductionUniversal` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.QuotientExpressionKFlatModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.QuotientExpressionKFlatNormalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.QuotientExpressionKFlatOperations` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.QuotientExpressionStrictKFlatTowers` | N3 | definitionally identical data; no adaptation |
| `Sheaf.Paper.RationalLatticeAdicDomain` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.RealizationCompletedImage` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.RestrictionOfScalarsExact` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.RoosAdjunctionQuotientNormalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ScalarReductionCochainComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SequenceKInjectiveComparisonShifts` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfAmbientIntegralDirectImage` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfClopenLisseCompleteLocalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfClopenRestrictionData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfCompleteDirectImageReduction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfConstructibleHeart` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfDerivedComplete` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfDerivedCompleteLegacyComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfDerivedDirectImage` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfDirectImageReductionTransitions` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfExceptionalReductionTransitions` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfImmersionCompletedPullbackComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfIntegralCompactSupportTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfIntegralConstructible` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfIntegralConstructibleLinear` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfIntegralConstructibleTriangulated` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfIntegralDirectImageConstructible` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfIntegralDirectImageShiftComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfIntegralOrdinaryRecollementRealization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfIntegralReductionConservative` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfIntegralReductionTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfOpenReductionAdjunctionTransport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfRationalBoundedConeTorsion` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfRationalSupportedAdjointTransport` | R5 | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfStrictDirectImageScalarData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SignedTwistReductionComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SmoothPurityTowerDerivedComplete` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SmoothPurityTowerFiniteReduction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SmoothPurityTowerReconstructionData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.StrictDvrCoefficientSequence` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.StrictDvrFlatTensorSequence` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.StrictDvrReductionTriangles` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SuccessiveReductionConstructibility` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SupportedTorReductionPropagation` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.TransportedReductionPullbackNormalized` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.TransportedReductionScalarNormalized` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.TransportedReductionSystemsNormalized` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.WfConstructibleTensorKoszulUnit` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ZlFiniteCompletedImageComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.CoefHomTowerScalarModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.CompactSupportProperImageTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.CompleteLiftedTopCellTriangle` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.CompletedCoefficientFreeResolution` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.ConstantScalarQuotientComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.IntegralOpenExtensionComplete` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.IntegralOpenReductionDefinitions` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.IntegralOpenReductionQuotientSquare` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenDvrAugmentedReductionComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenDvrAugmentedTowerComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenDvrIntrinsicCriterion` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenDvrIntrinsicOpenTransport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenDvrLimitComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenQuotientKoszulCompleteness` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenQuotientKoszulModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenSemilinearOrdinaryComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenSemilinearReductionDescent` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenSemilinearTensorModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenSemilinearTensorModelData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.ProEtale.IntegralCompletionPresentation` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquares` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.ProEtale.IntegralPresentationEncoding` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.ProEtale.IntegralReductionTransitionComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.ScalarModelAssociativity` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.ScalarModelUnit` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.StrictQuotientCompletionUnit` | unclaimed | definitionally identical data; no adaptation |

## Status

landed 20261026T102415-L-355579 2026-10-26 (merge of deliver/W2/Sheaf.Paper.IntegralOperationRoosEffectivity)
