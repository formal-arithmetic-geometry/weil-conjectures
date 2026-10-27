# AlgebraicGeometry.ProEtale.ReductionExceptionalRealization

## Reason

The retained proof needs separate realization, chart calculation and global
conservativity lemmas. Their statements use the existing interface of the assigned
module. Move this interface verbatim to an objects module, publicly reexported by
the assigned module, to avoid importing the theorem being proved from its own proof
lemmas. This changes no construction, signature, visibility, attribute or target meaning.

The previous head `22b4d1d4245` passed independent review but was not landed:
the reviewer's plain `.md` override name was rejected. This repository file is
`coord/changes/K5-reduction-exceptional-interface-relocation.md`. If the reader
supplies a corrected copy through `--apply-fixes`, `tools/batch_land.py` expects
that copy to be named `K5-reduction-exceptional-interface-relocation.change.md`.
This repair refreshes the consumer table against the current shared source.

## Old

`lean/Sheaf/SecSmoothPurity/ReductionExceptional.lean`, every line preceding the
main theorem docstring, is the old interface. Its complete text is retained verbatim
in the new module, including the copyright/header, imports, options, comments, all
definitions and proved helper theorems. In particular the realization record is:

```lean
structure ReductionExceptionalRealization (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (hF : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (G : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (adj : reductionCtfCompactSupport A j p hF ⊣ G) where
  /-- An ordinary-etale origin of every Dctf input. -/
  origin : spFiniteConstructibleTorCategory Y A ⥤
    Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y
  /-- The origin is bounded constructible of finite Tor amplitude. -/
  origin_ctf : ∀ K, Etale.DerivedCategory.boundedConstructibleFiniteTor
    (ULift.{u + 1, u} A) Y (origin.obj K)
  /-- The origin recovers exactly the original intrinsic object. -/
  originIso : origin ⋙ reductionSite A Y ≅ (spFiniteConstructibleTor Y A).ι
  /-- The ordinary right adjoint for the identical fixed compactification. -/
  right : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y ⥤
    Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X
  /-- Its actual ordinary-etale adjunction. -/
  adjunction : Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)) ⊣ right
  /-- Its values on the origins lie in the bounded-below comparison domain. -/
  right_plus : ∀ K, DerivedCategory.TStructure.t.plus (right.obj (origin.obj K))
  /-- The exceptional output comparison. -/
  rightIso : G ⋙ (spFiniteConstructibleTor X A).ι ≅ origin ⋙ right ⋙ reductionSite A X
  /-- The output comparison retains the actual transported counit. -/
  counit : reductionRealizationCounitEquation A j p hF G adj
    origin originIso right adjunction right_plus rightIso

```

## New

Exactly the same declarations and bodies, in
`lean/Sheaf/SecSmoothPurity/ReductionExceptionalObjects.lean`.

Private declarations do not travel through the public reexport. One importer,
`Sheaf.Paper.ChartCounitScalarTransport` (unclaimed), reads the private
`reductionTateOrdinaryScalar_isIso` through `import all Sheaf.SecSmoothPurity.ReductionExceptional`
(its line 265) and fails with `Unknown identifier` against the relocated interface.
The original module therefore also has `import all Sheaf.SecSmoothPurity.ReductionExceptionalObjects`
and re-declares `reductionTateOrdinaryScalar_isIso` as a private theorem with the identical
statement, proved by the relocated one (reviewer correction, 2026-10-26, re-applied to head
bc7ac73ba9c7). With it `ChartCounitScalarTransport` compiles unchanged. No other importer
reads a private declaration of the original module.
The original module has `public import Sheaf.SecSmoothPurity.ReductionExceptionalObjects`.
No declaration is removed from its public interface. The two existing DAG attachments
are updated; the new objects node owns the relocated interface.

## Users

The transitive consumer list below is from `tools/downstream.py`; no consumer requires
an adaptation (the private-access correction above keeps ChartCounitScalarTransport unchanged). The public reexport preserves both statement and proof imports. The table retains
previously recorded consumers and includes all current transitive consumers after
the returned delivery was reconciled with current sheaf-dag.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization` | G2 | Unchanged: public reexport of original declarations. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicCommonStageHomTranspose` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicExceptionalNormalizationMate` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicNormalizedPurityLift` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicOperationDomainsSourceComparison` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicPurityCanonicalSourceCoherence` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicPurityNormalizedComparisonConstruction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicPurityScalarNaturality` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicPurityScalarNaturalityData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicUnitTraceCounitReductions` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicUnitTraceProjectionAssembly` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicUnitTraceTargetNormalization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicUnitTraceTensorCoordinates` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdicUnitTraceTransposeReductions` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AffineCompactificationComparisonNormalization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AffineCounitScalar` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.AffineLineCanonicalScalarCounit` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.BrownTowerBoundedTransport` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.BrownTowerFiniteEvaluation` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.BrownTowerFiniteSiteComparison` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.BrownTowerGeometricTransport` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.BrownTowerRealization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.BrownTowerSite` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CartesianSectionAdjointMates` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CartesianSectionData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.ChartCounitScalarTransport` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CoefficientMapGeometricSquares` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CommonStageSmoothOperationIdentification` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CompactSupportCondensedRealization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CompactSupportRealizationFactorNormalization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CompactSupportRealizationFactorization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CompactSupportTowerReduction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CompositionComparisons` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CondensedExceptionalReconstruction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CondensedOpenCoefficientModels` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CondensedOpenCounitComparisons` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CondensedOpenCounitRealization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CondensedOpenCounitRealizationSupport` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CondensedOpenCounitUnits` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.CondensedOpenUnitComparison` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.EtaleAffineProjectionCoefficientMate` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.ExceptionalRealizationNormalization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.ExceptionalReconstructionComparison` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.ExceptionalReconstructionContext` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.ExceptionalReconstructionPresentations` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.ExceptionalRefinementMates` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FieldExceptionalSystemAdjoints` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FieldExceptionalSystemComparison` | M9 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FieldExceptionalSystemComponents` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FieldExceptionalSystemDomains` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FieldExceptionalSystemEvaluation` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FieldExceptionalSystemFiniteComposite` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FieldExceptionalSystemIso` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FieldExceptionalSystemLaws` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FieldProjectionSystemSquare` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FilteredCondensedCanonicalComparisons` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FilteredCondensedCounitBijective` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FilteredCondensedCounitFiniteFormula` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FilteredCondensedRepresentingPair` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FilteredCondensedRepresentingPairData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteAdjointCompositorTransposes` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteDiagonalBaseChangeReduction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteDiagonalDncReduction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteDiagonalOrientationAssembly` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteDiagonalOrientationReduction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteDiagonalReductionComparisons` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteDiagonalVectorReduction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteFreeCoefficientExtensionData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | P8 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteGammaEvaluationIsIso` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteOrientationReduction` | W9 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteReductionPositiveLineComparison` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteReductionTensorFactors` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteReductionTensorPurity` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteReductionThetaFactor` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.GeneralCondensedWeilRealization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.GeneralHomComparisonCocycles` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.GlobalIdentityNormalization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.GlobalVerdierDualityData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.IntegralAdjunctionBijection` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.IntegralAdjunctionReconstruction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.IntegralAdjunctionSourceComparison` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.IntegralCompositorLimitRealization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.IntegralOrientationReductionInjectivity` | U6 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.IntegralReconstructionComparisonData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.IntegralReconstructionComparisons` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.InverseContravariantBidual` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.LevelwiseNormalizedAdjointDescent` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.MixedCupCoefficientChange` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.MixedCupCoefficientSquare` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.MixedCupFieldCoordinates` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.MixedCupFieldNormalization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.MixedCupFieldOperations` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.MixedCupOperationComparisons` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.MixedCupRingedNormalization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.MixedCupTensorClosure` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.MixedCupTensorComparisons` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.MixedCupTensorElementary` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.MixedCupTensorNormalization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.NativeWeilScalarFrobeniusCounit` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | X3 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.NormalizedStageCoefficientCalculus` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.OrderedLineLevelBounds` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.OrderedTateScalarNormalization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.OrderedTowerOrientation` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.OrientationGroundFieldRetagging` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.ProEtaleCtfPullbackDomains` | V2 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurCoordinateRepresentingFamily` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurIntegralRepresentingPair` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurIntegralRepresentingPairData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurIntegralSupportComparison` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurIntegralSupportComparisonData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurIntegralSupportDerivedComparison` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurIntegralSupportOrdinaryComparison` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurRepresentingPairFiniteScalar` | V6 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurSupportPresentationAlpha` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurityConjugatesTowerReduction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurityFiniteReductionTransport` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurityPullbackLevelBounds` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurityPullbackReductionTransport` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.PurityTowerReductionComparisons` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RamifiedReductionComparisonSquare` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RamifiedScalarSystemTranspose` | B4 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RationalExceptionalFinalEquations` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RationalPurityCoherenceDescent` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RationalPurityComparisonDescent` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RationalPurityScalarLocalization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RationalPuritySourceLocalization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RationalScalarComparisonData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RationalScalarComparisonIdentification` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RawChartScalarCounitPasting` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.ReconstructedPairRefinementCoherence` | A5 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.ReductionSiteCoefficientPasting` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RefinementFiniteOriginEvaluation` | T9 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.RetaggingCoefficientTowerTransfer` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | K3 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SfPackageExceptionalCoherenceRealization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SfPackageFieldOperationRealization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SmoothOperationCoefficientComparisons` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SmoothOperationCoefficientModels` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SmoothOperationDescentSpecification` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SmoothOperationIdentificationSpecification` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SmoothPurityFieldExtension` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SmoothPurityTowerGamma` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SmoothPurityTowerGammaData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SmoothPurityTowerGluing` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SmoothPurityTowerGluingData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SmoothPurityTowerReductionTranspose` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SystemProjectionFormulaCoherence` | U6 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.SystemScalarProjectionIdentification` | V8 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TensorTransposeFiniteEvaluation` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TensorTransposeTowerNaturality` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TowerAdjointCompositorRealization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TowerCompositorFiniteEvaluation` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TowerNormalizationPreservation` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TowerPurityAdjointTransport` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TowerTensorAdjointDomains` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TowerTensorTransposeEvaluation` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TowerTensorTransposeWords` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackAdicAgreement` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackAdicIdentification` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackCanonicalShifts` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackCoefficientCoherence` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackPbcCoordinates` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackPbcPullback` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackPbcTwist` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackScalarFamilies` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackScalarPrimitives` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackScalarShifts` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackShiftCoherence` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackSquareCoordinates` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackSquareMaps` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackSquareScalars` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackSquareShiftEquations` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackTowerBounds` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackTowerDomain` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackTowerDomainDefinitions` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.TwistedPullbackTowerOrigins` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.VerdierCoefficientRealization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.VerdierHomChainComposition` | N3 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.WeilBaseChangeSemilinearPasting` | T2 | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.WeilChosenDualityExchange` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.WeilChosenDualityExchangeData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.WeilChosenExchangeConstruction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.Paper.WeilChosenTransposeNaturality` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingExponent` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | C8 | Unchanged: public reexport of original declarations. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | P2 | Unchanged: public reexport of original declarations. |
| `Sheaf.SecSmoothPurity.Reduction` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SecSmoothPurity.ReductionOrientation` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.AffineDualizingCoefficient` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | T8 | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | V1 | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | V3 | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.DualizingSupportEvaluation` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.FiniteScalarMateData` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.FiniteScalarMateRealization` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.IntegralDualExceptionalSystem` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.IntegralExceptionalDescendedCounit` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction` | T6 | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingSystem` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.RamifiedScalarExceptionalLimit` | B8 | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | Unchanged: public reexport of original declarations. |
| `Sheaf.SixFunctors.WeilChosenDualityHom` | unclaimed | Unchanged: public reexport of original declarations. |

## Status

landed 20261025T211641-L-4013015 2026-10-25 (merge of deliver/K5/Sheaf.SecSmoothPurity.ReductionExceptional)
