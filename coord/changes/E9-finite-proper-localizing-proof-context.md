# AlgebraicGeometry.ProEtale.finiteProperLocalizing

## Reason

Prove the proper localizing and base-change clauses with the current coefficient encodings.
The proof uses the already proved source coproduct theorem on complexes with etale-origin
cohomology and the finite proper generator comparison. Proved private helpers extend the
preservation and the specified exchange to the localizing closure. No existing declaration
signature, public import, coefficient construction or canonical map is changed.

The proof context reuses the finite proper theorem's cached instances, gives the large
canonical derived functors local irreducibility, and uses transparency-aware unification in
the geometric proofs. These choices prevent unfolding the resolving and monoidal structures.
The added imports are private proof imports, including `import all` for existing private
proved helpers and the hidden body of `finiteProperExchange`. The public universe `u` is
unchanged; the additional universe names are used only by private categorical lemmas.
No consumer needs adaptation and no target meaning changes.

## Old

```lean
set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor CategoryTheory.Obj
```

The two public theorems `finiteProperLocalizing` and `finiteProperLocalizing_baseChange`
have their existing signatures and proofs `by sorry`.

## New

```lean
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor CategoryTheory.Obj CategoryTheory.MonoidalClosed

attribute [local instance] finiteProperCache1 finiteProperCache2 finiteProperCache3
  finiteProperCache4 finiteProperCache5 finiteProperCache6 finiteProperCache7
  finiteProperCache8 finiteProperCache9 finiteProperCache10 finiteProperCache11 finiteProperCache12
  cachedModuleMonoidal cachedModuleBraided cachedModuleSymmetric cachedDerivedMonoidal
  cachedModuleClosed cachedModuleFlatResolution cachedDerivedTensorStructure

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [-instance] CategoryTheory.sfbSheafTensor_monoidalPreadditive
attribute [-instance] CategoryTheory.sfbSheafTensor_hasWeakSheafify
```

The cached tensor comparison properties are proved private theorems. Sequential
elaboration is enabled so each comparison helper is checked before its concrete uses.
The new private geometric proof block also marks the canonical derived functors,
monoidal structures, pullback compositor, adjunction and exchange locally irreducible.
The per-theorem `backward.isDefEq.respectTransparency` options then keep them abstract.
All four public theorem signatures and all definition bodies remain as before, except
that the existing admissibility proof uses `continuous_of_discreteTopology` explicitly
and registers its proved monoid-homomorphism property as a local instance.
There are no new public declarations and no new holes.

## Users

`tools/downstream.py Sheaf.Paper.FiniteProperLocalizing --uses finiteProperLocalizing
finiteProperLocalizing_baseChange finiteOpenLocalizing finiteCompactificationLocalizing`
reports 415 transitive consumers. Only `Sheaf.SixFunctors.ProperImageLocalizingProper`
textually uses these theorem names outside the item. Since all signatures and public
imports are unchanged, every consumer has the same interface and requires no source edit.
No other group's module is adapted. Holder status is immaterial to unchanged consumers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteProperLocalizing | E9 | Proper localizing proof completed; base-change proof remains an existing hole; public interface unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.AffineCompactificationComparisonNormalization | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.AffineCounitScalar | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.AffineLineCanonicalScalarCounit | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.BrownTowerBoundedTransport | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.BrownTowerGeometricTransport | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.BrownTowerRealization | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.BrownTowerSite | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CartesianSectionData | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ChartCounitScalarTransport | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ChartGeometricCounitEvaluation | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CoefSupportOpenTensorModel | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsData | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CondensedHomChainRealization | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperScalarComparison | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.EtaleCtfChartDomain | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.EtaleSumCounitScalar | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportDomains | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteTorStability | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.GeometricGeneratorProjectionDevissage | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.GeometricOperations | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.MateOpenCompactSupportExchange | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.MateOpenProperRestrictionIso | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.MateOpenProperSupport | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.MateOpenRestrictionMaps | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.NormAlgClInternalHomBaseChange | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.OpenExceptionalScalarLocality | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.OpenProEtaleCounitScalar | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.OrderedTateScalarNormalization | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.P1CounitScalar | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.P1SplittingScalar | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ProperAlgClComparisonDomains | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RationalAffineTensorCalculus | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RationalP1AmbientComposites | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RationalP1KernelContractions | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RationalP1Triangle | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RationalP1UnitCounit | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RawChartScalarCounitPasting | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ReductionSiteCoefficientPasting | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RelativeKunneth | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.RestrictionLocal | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SfBidualityClass | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGamma | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluing | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SupportedLatticeNormProjection | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.TamePairProperGenerators | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.TateTwistedProjection | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.VerdierExchange | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SecSmoothPurity.Reduction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CoefPairingFiniteNormalization | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteCounitRestrictionSquare | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionFunctors | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierModels | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCtf | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.ScalarSixDirectImage | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Targets.PoincareUncurry | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | not queried; unchanged | Same public interface; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | not queried; unchanged | Same public interface; no adaptation. |
| TargetsCheck | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.Statement | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.Additivity | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.Basic | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.BorelMoore | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.CompactPullback | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.CorrespondencePair | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.CurvePieces | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.FibreCoherence | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.FibreModel | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.FixedPointScheme | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.GenericQuotient | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.HomologyUnit | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.KunnethVerdier | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.LocalTerm | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.Main | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.ModelExtension | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.OpenSquare | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.Product | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.ProperCompatibility | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforward | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.PullbackFamily | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobenius | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.Statement | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.SupportedPairing | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.TraceClass | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.WeilBaseChange | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | not queried; unchanged | Same public interface; no adaptation. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | not queried; unchanged | Same public interface; no adaptation. |

## Status

landed 20261025T180630-L-4013181 2026-10-25 (merge of deliver/E9/Sheaf.Paper.FiniteProperLocalizing)

The exchange-locus proof uses the canonical
`unboundedLocalizingPullbackCommShift` and transports exactness through the canonical
termwise comparison. No alternative shift-instance convenience import is retained.

The private comparison block is a scoped section: its instance-cache and opacity
attributes end before the original public coefficient definitions. The geometric
proof block reinstates the caches after coefficient admissibility. This preserves
the original definition elaboration context and public instance terms.
