# AlgebraicGeometry.Etale.FiniteSmoothPurity.normalExchange_exists

## Reason

The source concerns closed sections. The old Lean signature omitted both section equations,
and Geometry does not contain them. The finite disjoint-union counterexample is recorded
in the node statement_change and report. This is a source-faithful correction of a false
intermediate theorem, not a change to any Challenge target. Prove the corrected assertion
from the existing section Rees base-change and etale theorems, without new holes.

The only direct importer is Sheaf.Paper.FiniteSectionIntegratedSpecialization (unclaimed
in the current shared snapshot and current server claim directory). Its theorem already
assumes both equations, so its only adaptation supplies hs and hsprime at the call.

## Old

```lean
theorem normalExchange_exists
    {V S V' S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (g : V ⟶ S) (g' : V' ⟶ S')
    (s : S ⟶ V) (s' : S' ⟶ V') [IsClosedImmersion s] [IsClosedImmersion s']
    (b : S' ⟶ S) (q : V' ⟶ V) (cart : IsPullback q g' g b)
    (hsec : s' ≫ q = b ≫ s)
    (d : ℕ) [FiniteRingSectionDeformation.Geometry d g s]
    [FiniteRingSectionDeformation.Geometry d g' s'] :
    ∃ (ν : s'.ker.normalCone ⟶ s.ker.normalCone),
      IsPullback ν (Scheme.Hom.normalConeProj g' s')
        (Scheme.Hom.normalConeProj g s) b ∧
      s'.normalConeZeroSection ≫ ν = b ≫ s.normalConeZeroSection
```

Public imports: Sheaf.Paper.FiniteSmoothPurityMaps and
Sheaf.Paper.VectorPurityNormalization. Proof import:
WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange.

## New

```lean
theorem normalExchange_exists
    {V S V' S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (g : V ⟶ S) (g' : V' ⟶ S')
    (s : S ⟶ V) (s' : S' ⟶ V') [IsClosedImmersion s] [IsClosedImmersion s']
    (hs : s ≫ g = 𝟙 S) (hs' : s' ≫ g' = 𝟙 S')
    (b : S' ⟶ S) (q : V' ⟶ V) (cart : IsPullback q g' g b)
    (hsec : s' ≫ q = b ≫ s)
    (d : ℕ) [FiniteRingSectionDeformation.Geometry d g s]
    [FiniteRingSectionDeformation.Geometry d g' s'] :
    ∃ (ν : s'.ker.normalCone ⟶ s.ker.normalCone),
      IsPullback ν (Scheme.Hom.normalConeProj g' s')
        (Scheme.Hom.normalConeProj g s) b ∧
      s'.normalConeZeroSection ≫ ν = b ≫ s.normalConeZeroSection
```

Publicly import Sheaf.Paper.FiniteRingSectionDeformation, which owns Geometry and exposes
all objects of the statement. Privately import Sheaf.Paper.SectionReesBaseChangeEtale
for the proof. Remove the three original imports. The direct caller itself publicly
imports both original Sheaf modules and privately imports SmoothBaseChange already;
therefore it retains every name it needs. Its public declarations and imports are unchanged.
The node proof/proof_deps now record the actual existing lemmas; lean.statement includes
both section equations and statement_change lists all three DAG citers.

## Users

All 166 transitive users from tools/downstream.py are listed below. Textual search
for normalExchange_exists finds only the item and its one direct caller.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.CompositeProjectionCoefficients | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.CompositionComparisons | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.CondensedIntegralEndpoints | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.CondensedTateIntegralTower | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.CondensedTateIntegralTowerData | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionCompletedStrictLimit | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionComposition | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionIntegralComparisons | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionIntegralCoordinates | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionIntegralDescent | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionIntegralModels | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionLimitEquations | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionRationalComparisons | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionRationalDescent | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionRationalModels | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionReductionDescent | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionReductionLimits | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionStrictLimits | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionSystemCoordinates | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldExtensionTowers | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldOrientationSystemComparison | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldOrientationSystemComparisonData | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldOrientationSystemCoordinates | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldOrientationSystemFiniteOrientation | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldOrientationSystemHeart | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldOrientationSystemNormalizations | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldOrientationSystemRigidity | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldPuritySystemTranspose | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldPuritySystemTransposeBase | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldPuritySystemTransposeCompatibility | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldPurityTransposeArrows | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FieldPurityTransposeLevelWords | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteNormalizedOrientationScalar | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteOrientationReduction | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteProCoefficientCounitTransport | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FinitePuritySourceUnitReduction | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteSectionIntegratedScalar | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteSectionIntegratedSpecialization | unclaimed | Pass existing hs and hsprime to normalExchange_exists; all own signatures and visibility unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteSmoothNormalizedExistence | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteSmoothOrientationBaseChange | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteSmoothProQuotientTransport | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteSmoothZeroOrientationCoordinates | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.FixedPresentationUniformizerReductions | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.GeometricSmoothReconstructionSetup | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralAdjunctionBijection | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralCoefficientModelComparison | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralCompositorLimitRealization | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralEquivarianceMate | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralEquivarianceNaturality | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralGeometricComparisonData | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralGeometricComparisonRealization | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralGeometricPurityRealization | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralGeometricReindexingRealization | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralGeometricSupportRealization | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralGeometricTransposeIdentity | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.NormalizedIntegralTraceData | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.NormalizedTateTensorTower | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.NormalizedTateTensorTowerCore | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.NormalizedTateTensorTowerProperties | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.NormalizedTateTensorTowerZero | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.OrderedLineLevelBounds | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.OrientationScalarPropagation | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.OrientationScalarTowerTransport | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.PulledOrderedLineSingle | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.PurityConjugatesTowerReduction | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.PurityFiniteReductionTransport | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.PurityPullbackLevelBounds | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.PurityPullbackReductionTransport | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.PurityTowerReductionComparisons | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.QuotientInverseOrientation | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.SmoothOrientationPuritySquares | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.SmoothPurityBaseChangeData | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.SmoothPurityCompositionFactors | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.SpecifiedTowerAdjunctionCharts | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.StrictTateTensorTowerLift | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TateTensorNormalizedSquare | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TateTensorQuotientBalancing | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerFactorOrientation | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerFactorTensor | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerGeometricPurityAssembly | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerGeometricPurityData | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerGeometricPurityMate | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerIsomorphismPullback | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerMuEvaluation | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerPurityAdjointTransport | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerPurityPresentationRetagging | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerSemilinearPurityFactors | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerTateSplitNormalized | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerTensorAdjointDomains | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerTensorPresentationRetagging | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerTracePurityComparison | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerTracePurityComparisonData | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TowerTraceScalarCounit | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TransportCondensedStageRealization | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TransportIntegralBaseChangeRealization | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TransportIntegralChartRealization | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TransportIntegralCompositionRealization | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TransportIntegralCounitData | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TransportIntegralCounitRealization | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.TransportIntegralStageConstruction | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.UniformTowerTensorClosure | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.WeilEquivarianceOfPurityAndTrace | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Paper.WeilPurityEquivarianceData | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.SecSmoothPurity.NestedAffineChartFormulas | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.SecSmoothPurity.NestedAffineFormulaData | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.SecSmoothPurity.ReductionOrientation | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| TargetsCheck | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| WeilConjectures | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed | Transitive consumer; no occurrence of normalExchange_exists and no signature or proof change. |

## Status

landed 20261027T210004-L-1642220 2026-10-27 (merge of deliver/G3/Sheaf.Paper.FiniteSectionIntegratedSpecializationNormalExchange)
