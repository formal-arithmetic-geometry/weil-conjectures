# CategoryTheory.ConstantScalarRestriction.onDerived and canonical tensor definitions

## Reason

The full zero-hole proof exceeded the fixed 60-second file gate through repeated
elaboration of canonical tensor instances and transparent derived-functor data.
Naming these existing canonical structures and keeping `onDerived` as a regular
reducible definition prevents unnecessary expansion. The derived proof also reuses
existing normalized braided localization and native derived tensor APIs.

These are definition repairs in the held item, not changed mathematical data.
No target signature or source-library declaration changes. Targets using these
definitions require renewed independent statement review; their meanings are
preserved by definitional equality. No forced consumer adaptations are proposed.

## Old

```lean
abbrev onDerived : DerivedCategory (Modules J B) ⥤ DerivedCategory (Fixed J B) :=
  (restriction J B).mapDerivedCategory
```

There were no named `complexTensorMemo`, `derivedTensorMemo`, `ringMonoidal` or
`ringSymmetric` declarations. Typeclass search inserted their canonical bodies
at each occurrence. `fixedMonoidal`, `fixedSymmetric`, the ordinary comparison,
and the public compatibility definitions retain their written definition bodies.

## New

```lean
def onDerived : DerivedCategory (Modules J B) ⥤ DerivedCategory (Fixed J B) :=
  (restriction J B).mapDerivedCategory
```

The following named instances cache the previously synthesized structures:

```lean
@[instance_reducible]
def complexTensorMemo (D : Type dU) [Category.{dV} D] [Abelian D]
    [HasColimitsOfSize.{0, 0} D] [MonoidalCategory D] [MonoidalClosed D]
    [MonoidalPreadditive D] [BraidedCategory D] :
    MonoidalCategory (CochainComplex D ℤ) := inferInstance

/-- Cache the canonical K-flat localization monoidal structure.
Source: Stacks 06YT (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
@[instance_reducible]
def derivedTensorMemo (D : Type dU) [Category.{dV} D] [Abelian D]
    [IsGrothendieckAbelian.{dV} D] [HasColimitsOfSize.{0, 0} D]
    [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory.{dW} D] :
    MonoidalCategory (DerivedCategory D) := inferInstance

instance ringMonoidal : MonoidalCategory (Modules J B) := inferInstance

instance ringSymmetric : SymmetricCategory (Modules J B) := inferInstance
```

The two generic caches are registered only as local instances in this module.
The ringed instances choose the same canonical ringed sheaf structures as before.
All are definitions with constructed bodies, definitionally equal to the old
synthesized instances. No compatibility law is weakened. Generic private cache
wrappers and flat-resolution transport affect only proof elaboration.
`DerivedComparisonData` remains its original subtype with the same three laws.
`derived_isEquivalence` now explicitly changes to the unchanged mapped functor
before applying the existing equivalence instance.

The ordinary hole is filled by the explicit braided construction and pure-tensor
inverse calculation in `OrdinaryProof`. Private imports and local reducibility
attributes serve these proofs; they introduce no public mathematical hypotheses.

## Users

Enumerated with `tools/downstream.py` and its `--uses` option. The table includes
all transitive importers, a conservative superset of textual declaration users.
Direct textual users of `onDerived` are `ConstantModuleDerivedComparisonData`,
`ConstantModuleDerivedProjectionIdentification`, `ConstantModulePlusComparisonData`,
`ConstantModuleTensorSquareDescent`, `RamifiedScalarSystemTranspose`, and
`SystemRefinementConstructibleDomain`. `EtaleRingedProjectionPresentation` also
uses `DerivedComparisonData`. Their statements retain the same meanings because
the replacement definitions are definitionally equal. No downstream source edits
are required by an interface change; compile validation is reported separately.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.ConstantScalarRestrictionTensor` | U9 | Prove ordinary comparison and repair definition elaboration. |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralCompletedConstantModelTransport` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralConstantModelConstructibility` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralConstantModelRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralModelsCompletionTransport` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralModelsResidueTransport` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.CategoryTheory.ConstantModuleDerivedComparisonData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.CategoryTheory.ConstantModuleDerivedProjectionIdentification` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.CategoryTheory.ConstantModuleGeometricComparisonData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.CategoryTheory.ConstantModuleOrdinaryRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.CategoryTheory.ConstantModulePlusComparisonData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.CategoryTheory.ConstantModuleTensorSquareDescent` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.CategoryTheory.DerivedProjectionComparisonSquares` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel` | X8 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AdicCommonStageHomTranspose` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AdicExceptionalCompositorCoefficients` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AdicExceptionalCompositorCoefficientsData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | A6 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AdicNormalizedPurityLift` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AdicOperationDomainsSourceComparison` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AdicProperLocalizingAdjunctionComparison` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AdicRamifiedScalarCochainNormalization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AdicRamifiedScalarRealizationData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AdicUnitTraceTensorCoordinates` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AdicUnitTraceTransposeReductions` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AffineCounitScalar` | E1 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.AnchoredPureCurveCriterion` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | H2 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.BrownHypothesesGeneration` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.BrownTowerBoundedTransport` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.BrownTowerFiniteEvaluation` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.BrownTowerFiniteSiteComparison` | U5 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.BrownTowerRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.BrownTowerSite` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CartesianSectionAdjointMates` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CartesianSectionData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ChartCounitScalarTransport` | M9 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ChartDiagonalSourceMate` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ClassicalFiniteWeilDiagramRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilFrontierRestriction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilRestrictionData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilRestrictionMaps` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ClassicalNormalizedTwoFibreComparison` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ClassicalNormalizedTwoFibreData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ClassicalTwoFibreCommonData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ClassicalTwoFibreScalarData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ClassicalWeilFiltrationHeartTransport` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CoefSupportOpenTensorModel` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CoefSupportPointSectionsData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CoefficientGammaRepresentatives` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CoefficientTowerGeometricComposition` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CoefficientTowerSectionCoordinates` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CoefficientTowerTransitionCompatibility` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | A4 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CompactificationLocalizing` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CompactificationProjectionInverse` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CompactificationRefinementIdentity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CompleteIntegralResidueFunctor` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ConcreteIntegralProjectionCone` | D6 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ConcreteProjectionFieldDescent` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CondensedExceptionalReconstruction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CondensedHomChainRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ConstructibleCompactness` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperFiniteness` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperHeartFiniteness` | P3 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperLowerTail` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperScalarComparison` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.CurveRestrictionFiltrationSpectrum` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.DerivedTruncationCoproducts` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation` | W6 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleAffineProjectionCoefficientMate` | Y6 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleCtfChartDomain` | E2 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleOpenCounitFlatModels` | H1 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | Y7 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleRingedDerivedIdentificationData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleRingedDerivedNormalization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleRingedGeometricRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleRingedNativeDerivedComparison` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleRingedNativeTensorRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleRingedNormalizedConstraints` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleRingedProjectionIdentification` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleRingedProjectionPresentation` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.EtaleSumCounitScalar` | V5 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ExceptionalRealizationNormalization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionComparison` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionContext` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionPresentations` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FieldBoundedConstructibleTensor` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteAdjointCompositorTransposes` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | P8 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteCoefficientDerivedExchangeIdentification` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteCoefficientModelComparison` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteCompactSupportDomains` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteComparisonLocalizing` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteComparisonPresentation` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteComplexHeartFilteredApproximation` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteDiagonalOrientationReduction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteDiagonalReductionComparisons` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteEncodingTensorTor` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteExceptionalCompositorCoefficients` | F9 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | G6 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteLevelProjectionFactors` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteLocalizingSmoothLocalFormula` | C1 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteModelSheafQuotientConstructible` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteProperBaseChange` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteProperLocalizing` | E9 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteTorStability` | E5 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteWindow` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteWindowBounded` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FiniteWindowUnbounded` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.FrobeniusExchangeEquivalence` | K4 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.GeneralCondensedWeilRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.GeneralHomComparisonCocycles` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.GeneralLfpAdicInputWitness` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.GeometricComparisonData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.GeometricGeneratorProjectionDevissage` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.GeometricOperations` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.GeometricQuotientWeilCompositionSeries` | H8 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.HomChainPairingNaturality` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralAdicHomCompleteness` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralAdicHomResidueOrigin` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralAdicInputNormalization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralAmbientCoefficientPresentation` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralAmbientDirectImageEncoding` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralAmbientTowerComparison` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralCoefficientModelRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralConstantModelHeart` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleCompletionBridge` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleExt` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleHeart` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralCriterionReductions` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralGeneralLfpHomFiniteness` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralHeartDualizable` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralHeartLocalModel` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralHeartRealizationExact` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralHeartResidueDual` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | P4 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralModels` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralModelsEmbedded` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralModelsEmbeddedCompletion` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralModelsEmbeddedResidueComparison` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralModelsEmbeddedStacksCriterion` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralProperCohomologicalBounds` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralProperProjectionFormula` | K3 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralResidueClassTriangleClosure` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralSectionLocalModels` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralStratumExtBound` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralTensorProduct` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.IntegralTensorPullback` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.InterchangeProperPasting` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.InverseContravariantBidual` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.LevelwiseNormalizedAdjointDescent` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.LevelwiseNormalizedStrictSystems` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekCompositionModel` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.MateOpenRestriction` | F3 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.NativeAdicCompactSupportSums` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.NativeGeometricBrownConstructibleComparison` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.NativeWeilDerivedInductionComparison` | S1 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.NativeWeilLocalizingBrownAdjoints` | S2 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.NoetherianFiniteComplexHeartFilteredClosure` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.NoetherianScalarConstructibleHeart` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.NoetherianTorsionCdTopologicalSerreTransfer` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.NonrationalCompositionSeed` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.NormAlgClInternalHomBaseChange` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.NormalizedFiniteFibreModels` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.NormalizedFiniteRealizationFibre` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.OpenExceptionalScalarLocality` | J1 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.OpenImmersionLocalizing` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.OpenProEtaleCounitScalar` | F3 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.OpenScalarFlatModelRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.OpenScalarSiteCoherence` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.OrderedCompactificationScalarSquare` | H3 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.OrderedTateScalarNormalization` | H4 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.P1CounitScalar` | F4 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.P1SplittingScalar` | G1 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.PodCtfAdjunctions` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.PodCtfPairingMaps` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.PodHomChainCounitFormula` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.PodHomChainCtfDomains` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.PodHomChainUncurriedTransport` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.PointTraceReconstruction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProjectionFormulaCoherence` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProjectiveDiagonalComposition` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProperAlgClComparisonDomains` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProperHeartBoundLattice` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProperLocalizingAdmissibleCoefficients` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProperLocalizingContinuousAlgCl` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProperOpenBoundaryZero` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProperProductCounitTranspose` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProperUnboundedCoproductComparison` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProperUnboundedCoproducts` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ProperUnboundedWindowIso` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.PurIntegralRepresentingPair` | K9 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.PurIntegralSupportComparison` | M7 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.QcqsIntegralFiniteModelCompleteness` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RamifiedReductionComparisonSquare` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RamifiedScalarSystemTranspose` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalAffineAdjunctionCalculus` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalAffineTensorCalculus` | J6 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalLocalizedHom` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | U2 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalP1AmbientComposites` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalP1DiagonalTensor` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalP1KernelContractions` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalP1Triangle` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalP1UnitCounit` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalRestrictionGlue` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RawChartScalarCounitPasting` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ReconstructedPairRefinementCoherence` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RelativeKunneth` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RelativeProductInputDomains` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.RestrictionLocal` | C3 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SfPackageCoefficientDomains` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SfPackageExceptionalCoherenceRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SfPackageFieldOperationRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SfPackageLocalizationProjectionRealization` | S4 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.ShriekNormalizedTransitionComparison` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateCategories` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateRightComparisons` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateTensorComparisons` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGluing` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SmoothPurityTowerReductionTranspose` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SuccessiveReductionConstructibility` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SupportedImageKoszulComparisonNonpositive` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SupportedImageTorsionReductionsCd` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SupportedLatticeNormProjection` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SystemProjectionFormulaCoherence` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SystemRefinementConstructibleDomain` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.SystemScalarProjectionIdentification` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.TamePairProperGenerators` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.TateTwistedProjection` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.TensorHomCoefficientTransposes` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.TowerProjectionDomainEvaluation` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.TraceBaseChangeSecond` | P1 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.TraceCorrespondences` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.UniformConstructibleExt` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.UniformConstructibleExtIntegral` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.UniformConstructibleExtRational` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.VectorTraceScalarDescent` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.WeilChosenDualityExchange` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction` | G4 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization` | K7 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SecSmoothPurity.Reduction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | D3 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.CoefFinitePairingEvaluationData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.CoefPairingFiniteNormalization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.CoefPairingSystemDinaturality` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | V1 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.CoefSystemProjectionEvaluation` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | V3 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.CoefficientProjectionPointData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | G1 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.DualizingSupportEvaluation` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.FiniteCompactProetale` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.FiniteCounitRestrictionSquare` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.FiniteCtfInternalEtaleRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.FiniteExceptional` | X3 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.FiniteOpenDirectImageCtf` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.FiniteScalarMateData` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.FiniteScalarMateRealization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralAffinePurityInduction` | J9 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralComplementFiniteness` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralDualExceptionalSystem` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalDescendedCounit` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingSystem` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | D3 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralProjectiveLineAdjunction` | K5 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionFunctors` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralTateLineConstructible` | K6 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralTensorInverseImage` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | Y3 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | H7 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.ScalarCompositeModelPasting` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.ScalarRefinementClosureSquare` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.ScalarSixCompactSupport` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.ScalarSixCtf` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.ScalarSixDirectImage` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctors.WeilChosenDualityHom` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | R1 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | P2 | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `TargetsCheck` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | S6 | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingProjection` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | D9 | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.Statement` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.Additivity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.BaseChangeCoherence` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.BorelMoore` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.CoefficientMorphism` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.CompactCohomology` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.CompactPullback` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.Correspondence` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.CorrespondencePair` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.CurvePieces` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.Dualizing` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.FibreCoherence` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.FibreModel` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.FixedPoint` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.FixedPointScheme` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.Frobenius` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusLocalTerm` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.GenericQuotient` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.HomologyUnit` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.KunnethVerdier` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.LefschetzVerdier` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.LocalTerm` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.LocalTermLocality` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.Main` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.ModelExtension` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.OpenPieceCoherence` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.OpenSquare` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.PointNormalization` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.Product` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.ProperCompatibility` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.ProperCurve` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.ProperPushforward` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.ProperPushforwardKernel` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.PullbackFamily` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.RelativeFrobenius` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.RelativeFrobeniusComparison` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.RelativeFrobeniusIterate` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionInduction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.Stalk` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.SupportedPairing` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.TraceClass` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.TraceClassAdditivity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.WeilBaseChange` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.WeilSheafUpperStar` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.TraceFormula.WeilTrace` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Definitionally equal canonical data; no source adaptation. |
| `WeilConjectures.ZetaFunction.WeilObjectComparison` | unclaimed | Definitionally equal canonical data; no source adaptation. |

## Status

landed 20261024T234301-L-2549791 2026-10-24 (merge of deliver/U9/Sheaf.CategoryTheory.ConstantScalarRestrictionTensor)
