# AlgebraicGeometry.Etale.finiteRing_constant_derived_mapping_sheaves

## Reason

The proof adds private helper declarations, `open Opposite`, and elaboration options
(`autoImplicit` and backward definitional equality transparency). The static interface
scanner classifies these commands as an interface change. They change proof elaboration
only; no public declaration signature, definition body, public import, instance or
notation is altered. The public theorem statement is byte-identical to the original.

## Old

```lean
theorem finiteRing_constant_derived_mapping_sheaves
    (U : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (E G : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (hG : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hEfin : ∀ n : ℤ, Finite (E.X n)) (hGfin : ∀ n : ℤ, Finite (G.X n)) :
    Nonempty
      (((presheafToSheaf U.smallEtaleTopology (Type (u + 1))).obj
        (derivedHomPresheaf B
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E))
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G)))) ≅
        (constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
          (DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj G)) ∧
    Nonempty
      (((presheafToSheaf U.smallEtaleTopology (Type (u + 1))).obj
        (derivedIsoPresheaf B
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E))
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G)))) ≅
        (constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
          (DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj G))
```

The module previously had no `open Opposite` or local elaboration options after its
namespace header. Its theorem proof was `by sorry`.

## New

```lean
theorem finiteRing_constant_derived_mapping_sheaves
    (U : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (E G : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (hG : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hEfin : ∀ n : ℤ, Finite (E.X n)) (hGfin : ∀ n : ℤ, Finite (G.X n)) :
    Nonempty
      (((presheafToSheaf U.smallEtaleTopology (Type (u + 1))).obj
        (derivedHomPresheaf B
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E))
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G)))) ≅
        (constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
          (DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj G)) ∧
    Nonempty
      (((presheafToSheaf U.smallEtaleTopology (Type (u + 1))).obj
        (derivedIsoPresheaf B
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E))
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G)))) ≅
        (constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
          (DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj G))
```

The module additionally opens `Opposite`, sets `autoImplicit` to false, and disables
`backward.isDefEq.respectTransparency` and its `types` option for the private helper
proofs. Its complete proof uses the new local-representative theorem and exact stalk
faithfulness. The added commands export no declarations or instances.

## Users

`tools/downstream.py` lists 749 transitive importers. Only
`Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy` mentions this theorem directly.
The theorem signature and all existing exported definitions, instances and imports are
unchanged, so every consumer retains its existing meaning and needs no adaptation.
The complete downstream list and current claim holders are recorded below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | Q3 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoefficientMateDiagonalGraph | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization | X2 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentExtVanishing | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientPresentationIdentification | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedComponentInverseImage | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedComponentPullbackCompatibility | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLocalizationExactCohomology | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedProfiniteScalarCompatibility | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ContractibleEvaluationAdjunction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedHomSheafComparisonLisse | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | V1 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteLisseFieldDual | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteLisseFieldSitePerfect | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePullbackLocalizationCohomology | V7 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy | unclaimed | Two calls use the identical signature; no adaptation. |
| Sheaf.AlgebraicGeometry.FrobeniusFactorization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentCoefficientComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenModuleRestrictionIdentities | T2 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | K9 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarPresentationCokernel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | R9 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SheafExtCoherent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | D9 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Compactification.NagataDensityNormalizationSheaves | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.FieldTheory.CondensedSubfieldBasis | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.NumberTheory.Padics.BaseCoefficientCondensedIdentification | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.NumberTheory.Padics.FiniteIntegralCondensedResolution | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.AdicSmoothBaseChange | M9 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.AdmissibleScalarRealizationExact | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.AmbTateRootProjectionReduction | R4 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | P5 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.AutomorphismCompletionUnitComparison | E2 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | E2 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ClopenRoosIntegralDescent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ClosedSupportBoundedContinuity | U2 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientHeartTriangulated | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientProjectionSquare | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientPushFilteredLegs | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CohomologyTorInterval | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CommonStageCalculus | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CommonStageLisse | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CommonStageLocallyFree | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTower | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompatibleFiniteDerivedTrivializations | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompleteCompactSupportProetale | S3 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompletedCoefficientCompletionRoosTransport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompletedCoefficientPresentationTransport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | F6 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompletedExchangeCoherence | S9 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompletedLineTensorCoherence | J6 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompletedPerfectScalarPullback | B4 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompletedPullbackTensorComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompletedTensorScalarLinearity | E7 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CompletionTriangleComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedCompactSupportProjection | T2 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedERealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedPointCoefficients | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstantToContinuousScalarFlat | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstantWeilStructure | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstructibleRationalHomComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousCoefficientFreeRank | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CurveMiddleExtension | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DerivedExchangeExactNormalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DerivedNakayama | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DerivedNakayamaResolution | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DerivedPullbackTensorHom | S4 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DerivedPullbackTensorIso | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ECoefficientSmoothBaseChange | M7 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.EffectiveComparisonRealizationModels | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.EtaleIsoDescent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ExplicitExceptionalPreservation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteCoefficientModelComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteCoefficientPoint | T3 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteConstantModelResolution | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingCompactification | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingConstructibility | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingNaturality | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingTensorTor | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEncoding | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteFreeConstructibleScalarTransport | Z5 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteOpenProductSwap | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteProductFieldCoefficientDescent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteProjectionActionLaws | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteProperBaseChange | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteProperProductTranspose | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FinitePullbackTensorComparison | F8 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteStageRationalExchangeCoherence | P7 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteTateSiteDescent | T4 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FourierAdicArtinSchreier | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | A5 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.GeometricStalkPerfect | T5 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IdentificationFibreAdjunction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralCanonicalTruncations | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralCoefficientExtComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralCoherenceTower | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralCompositionCounitImages | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHomSums | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralCriterionReductions | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralDerivedCoefficientData | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalDualityDescent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralLineReductionRestriction | J8 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralModelsExtensionClosed | R5 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralProperReductionBound | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralPullbackReductionCounit | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralPullbackSystemComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralResidueClassTriangleClosure | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | H9 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralStratifiedPerfectClosureHomology | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralSystemPullbackLiftAssociativity | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralTStructure | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwists | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IntrinsicQbarCategory | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.InverseImagePullbackComparisonDerived | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IsomorphismComparisonNatural | R6 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.IsomorphismScalarTensorKFlatModel | S6 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.LisseNormalizedTowerLocalModels | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTrace | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.LocalModelTorBoundDescent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.LocalizedTStructure | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ModuleDerivedCompositorCoherence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.NormalizedDerivedIsomorphismSectionReduction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.NormalizedDerivedIsomorphismTransport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | K9 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | S4 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.OrdinaryPullbackStratifiedModels | G5 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PadicIntegersInvertEll | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcCohomologySheaves | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcCommonStageCones | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcConeIndependence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcConstructibleReductionCriterion | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcDescentFunctors | J5 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcDistinguishedDiagramLifting | A8 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcFiniteRawScalarComparison | S7 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcFiniteStageKaroubian | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcIdempotentCompleteTriangulation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcPairFunctorShiftCoherence | A3 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcQbarCategory | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcQbarCompletedPullback | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcQbarIdempotentComplete | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcQbarStandardCohomology | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcRationalTransport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcScalarExtension | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcSupportCondition | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcUniformCompleteTriangulated | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcUniformReductionCriterion | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PbcVerdierAxioms | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointAutomorphismRestrictionNatural | R7 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointExactDerivedModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensor | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorBasic | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorFiniteModels | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorModels | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorQbar | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorRational | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorScalar | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointFibreEquivalence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointIntegralPerfectRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointIntegralSectionsConservative | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointQbarFibreShiftDescent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointRationalFibreExact | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointRationalSectionsHom | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointRationalSectionsLattice | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointSectionsReconstruction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PointTransformationCoefficientDescent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PrincipalReductionConeCalculus | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ProjectionSectionNormalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ProperHeartBoundTorsion | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowBounded | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PulledReductionStrictTowerComparison | M1 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PurityConventions | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PurityFiniteKummerLevel | A9 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PurityFiniteOpenIntervalDescent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | G6 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | M8 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.QbarIdempotentComplete | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.QuotientSystemMixedCoherence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.RationalModuleRealizationFunctor | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.RealSheafSections | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.RealWeilSheaves | R8 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.RealizationCompletedPull | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.RealizationScalarFunctor | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ResidueLisseProjectiveModels | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ScalarExtensionExactIntrinsic | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SectionDerivedPushpullNormalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SectionDerivedRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SectionDerivedTensorNormalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SectionOrdinaryOplaxNormalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfAlgebraicallyClosedCoefficients | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | P8 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfConstructibleCanonicalCompleteness | G2 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfConstructibleHeart | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfExactPullbackCounitNormalization | G9 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfIntegralConstructibleLinear | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfIntegralConstructibleTriangulated | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfIntegralStandardTruncations | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfOpenReductionAdjunctionTransport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfRationalBoundedConeTorsion | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfRationalizationKaroubi | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfScalarExtensionComposition | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SfWeilSheafComplex | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SitePerfectComplex | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.StratifiedLattice | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.StratifiedPerfectInternalHomCoproducts | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SupportedCupFunctoriality | P9 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SupportedHomCocycleNormalization | H5 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SupportedHomPullback | B8 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.TwoTermReductionCohomology | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.WeilComplexQbarIdempotentComplete | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.WeilKernelHenselianInertia | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SecSmoothPurity.WeilTwistRationalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.FiniteOpenDirectImageCtf | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.IntTensorProjection | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.OpenScalarConjugateNormalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.OpenSemilinearTensorModel | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralCompletionPresentation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralPresentationEncoding | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ScalarSixPullback | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.SchemeFrobenius | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisComparison | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Topology.ProfiniteCondensedRing | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Topology.ProfiniteSectionsFiniteQuotient | U3 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.Topology.TopologicalModuleCondensation | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.TraceFormula.IntegralComparisonCounitCharacterization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | H7 | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.TraceFormula.PointTransportComposition | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| TargetsCheck | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Homology | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Transitive importer; no exported statement or definition changes; no adaptation. |

## Status

landed 20261021T134258-L-748474 2026-10-21 (merge of deliver/B2/Sheaf.AlgebraicGeometry.FiniteRingConstantDerivedMappingSheaves)
