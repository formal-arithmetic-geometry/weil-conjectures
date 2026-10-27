# WeilConjectures.PurityConventions import dependencies

## Reason

Restore the assigned quarantined item with every declaration, signature and data construction
retained. The archived aggregate imports of ProEtaleTateTwists, PurityFiniteKummerLevel and
PbcCoefficientTwists reach SfP1ProjectionTraceFalseTail. The statements in this module use
only the finite root-tensor construction, affine coordinate and conormal algebra, so use
those existing lower modules directly. This removes the offending dependency without
replacing any mathematical object or withdrawing any declaration.

Apply the archived torsor import migration recorded in
coord/changes/retire-etale-torsor-h1-functoriality-J5.md: the same proved theorem is in the
adopted source library. It is needed only by the torsor proof, so import it privately.
The published finite coefficient instance and annihilator are explicitly imported from
FixedFinitePositiveCoefficientTwist. The original normal-cone and finite-Tor convention reexports are retained.
No source-library module, target signature, statement, definition formula or instance is edited.

## Old

The archived import block, verbatim:

```lean
public import Sheaf.Paper.ProEtaleTateTwists
public import Sheaf.Paper.PurityFiniteKummerLevel
public import Sheaf.Paper.PurityAffineLineDatum
public import Sheaf.Paper.PurityNormalBundle
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
public import Sheaf.AlgebraicGeometry.KummerModuleCoefficients
public import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
public import Sheaf.Paper.ComparisonPullbackExact
public import Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality
public import WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
```

## New

The replacement import block, verbatim:

```lean
public import Sheaf.Paper.TateTwistFiniteLocallyFree
public import Sheaf.Paper.PurityAffineLineDatum
public import Sheaf.Paper.PurityNormalBundle
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
public import Sheaf.AlgebraicGeometry.KummerModuleCoefficients
public import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
public import Sheaf.Paper.ComparisonPullbackExact
public import WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Paper.FixedFinitePositiveCoefficientTwist
import WeilConjectures.CategoryTheory.Sites.EtaleTorsorH1Functoriality
```

The other changes fill existing theorem proofs only. The unique normalized choices remain
the same mathematical maps; the coefficient ring and its finite root-tensor line are the
published constructions. No target definition changes meaning or requires statement re-review.

## Users

Inventory from tools/downstream.py Sheaf.Paper.PurityConventions --names. Claims below
are recorded at preparation time. All declaration signatures and data formulas stay identical.
Direct consumers are checked with lcompile.py; unchanged test copies are removed before delivery.
No downstream module is intentionally adapted. Direct checks found no type errors: 15 of 18
completed below 60 seconds; three large unclaimed consumers exceeded the timing limit. Their
temporary copies were removed and no consumer interface or body was changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedOpenCounitTensorAction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineLineTensorCounit | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTensorActions | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTowerTensorCounit | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1TensorAction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicActualSystemsNormalized | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicNormalizedPuritySystems | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicPuritySourceNormalization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicPuritySourceTransitionSquare | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineCounitScalar | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineDiagonalDncCoordinateIdentity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineDiagonalDncNormalization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineDiagonalIntegrationConstructions | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.AffineDiagonalIntegrationTranslationIntegration | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineDiagonalIntegrationTranslationTranspose | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineDiagonalPowerCoefficient | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineDiagonalPresentedBaseChange | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineDiagonalRawTransposePower | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineDiagonalRestrictedTransposes | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineDiagonalSectionCoordinates | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineDiagonalTraceRestriction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineDiagonalTransposePower | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineIntegrationExponentTransition | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineOrderedCounitDescentComparison | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineOrderedCounitSuccessor | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineOrderedCounitZero | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CartierRelativeBoundaryRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CartierSupportedComparisonSquare | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CentredDiagonalSourcePasting | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChartCounitScalarTransport | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChartDncNaturality | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChartDncSquare | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChartDncVectorFactorData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChartEpsilonPasting | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChartIntegrationAdjoints | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CochainLocalizationTensorIso | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationCore | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationShift | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ComparisonImageClosedSectionNormalization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CompositeProjectionCoefficients | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CompositionComparisons | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CompositionIteratedMateExpansion | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CompositionSingleMatePresentation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CondensedIntegralEndpoints | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CondensedTateIntegralTower | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CondensedTateIntegralTowerData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.DiagonalDncChartNormalization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.DiagonalExchangeCube | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionCompletedStrictLimit | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionComposition | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionIntegralComparisons | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionIntegralCoordinates | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionIntegralDescent | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionIntegralModels | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionLimitEquations | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionRationalComparisons | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionRationalDescent | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionRationalModels | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionReductionDescent | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionReductionLimits | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionStrictLimits | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionSystemCoordinates | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldExtensionTowers | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldOrientationSystemComparison | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldOrientationSystemComparisonData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldOrientationSystemCoordinates | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldOrientationSystemFiniteOrientation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldOrientationSystemHeart | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldOrientationSystemNormalizations | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldOrientationSystemRigidity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldOrientedExchangeSquares | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldPuritySystemTranspose | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldPuritySystemTransposeBase | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldPuritySystemTransposeCompatibility | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldPurityTransposeArrows | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FieldPurityTransposeLevelWords | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteGeometricOrientationExchange | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteGeometricPurityCoordinates | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteGeometricPurityFactors | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteGeometricTensorExchange | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteNormalizedOrientationScalar | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteOrientationReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FinitePositiveChartFrameExt | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FinitePositiveRootChartPower | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FinitePublishedRootChartPower | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FinitePuritySourceUnitReduction | H3 | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionBaseChangeSource | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionLineChartScalars | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionLineInputConstructible | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionReassociation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionShiftedPullbackCube | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionTensorSource | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteRingSectionDeformation | R1 | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteRootLinePowerTransition | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteScalarCochainComparisonIso | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteScalarMonoidalRepresentative | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteScalarRepresentativeIso | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteScalarTensorData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteScalarTensorSource | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSectionIntegratedScalar | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSectionIntegratedSpecialization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSmoothDiagonalScalar | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | R3 | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | M3 | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSmoothOrientationBaseChange | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | K1 | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | K2 | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSourceChartPowerTransition | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSourceChartScalarTransition | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTateBalancedScalarPullback | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTateScalarSourceData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTateScalarSourceExistence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTateScalarSourceNormalization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTateSourceMap | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTateSourceStructuralCoherence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorLineChartReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorLineDerivedExistence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorPresentationReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorProductFrameExt | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorProductMap | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorProductMapIsIso | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorPullbackCompositionReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorPullbackTensorReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorSemilinearReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorShiftCoherence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorShiftFirst | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorShiftSecond | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorSignedReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FixedPresentationUniformizerReductions | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.GeometricSmoothReconstructionSetup | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralAdjunctionBijection | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralCoefficientModelComparison | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralCompositorLimitRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralEquivarianceMate | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralEquivarianceNaturality | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralGeometricComparisonData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralGeometricComparisonRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralGeometricPurityRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralGeometricReindexingRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralGeometricSupportRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralGeometricTransposeIdentity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.IteratedTateSourceComposite | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.NormalSectionIntegrationBaseChange | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.NormalSectionIntegrationData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.NormalSectionIntegrationOrientation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.NormalizedDivisorFamilyPullback | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTrace | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.NormalizedIntegralTraceData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.NormalizedTateTensorTower | J1 | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.OrderedLineLevelBounds | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.OrderedTateTowerCohomology | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.OrderedTowerOrientation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.OrientationScalarPropagation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.OrientationScalarTowerTransport | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.P1CounitScalar | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PoincareDualityConventions | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ProjectionTensorIntegration | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ProjectionUnitPresentationNormalization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PulledOrderedLineSingle | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityCompactSupportTransport | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityConjugatesTowerReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.PurityFiniteReductionTransport | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityFiniteTateSourceComparisonCalculus | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityKappaStages | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityOrientationDatum | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityPullbackLevelBounds | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityPullbackReductionTransport | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityTateDatum | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityTowerReductionComparisons | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.RationalPurityExchangeEndpointData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.RationalPurityExchangeEndpoints | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.RationalPurityLocalizedFamilyData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.RawChartScalarCounitPasting | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SectionEtaleOpenCancellation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothExchangeScalarCompatibility | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothOrientationPuritySquares | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothOrientationStageExchange | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothPurityBaseChangeData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothPurityCompositionFactors | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SmoothPurityTowerGammaData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SpecifiedTowerAdjunctionCharts | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Direct consumer; compile against the delivered import interface. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TateScalarPullbackCoherence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TensorTransposeTowerNaturality | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerFactorOrientation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerFactorTensor | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerGeometricPurityAssembly | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerGeometricPurityData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerGeometricPurityMate | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerIsomorphismPullback | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerMuEvaluation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerNormalizationPreservation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerOrientationEvaluation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerOrientationWordNormalization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerPurityAdjointTransport | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerPurityPresentationRetagging | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerSemilinearPurityFactors | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerTateSplitNormalized | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerTensorAdjointDomains | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerTensorPresentationRetagging | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerTensorTransposeWords | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerTracePurityComparison | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerTracePurityComparisonData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TowerTraceScalarCounit | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TransportCondensedStageRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TransportIntegralBaseChangeRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TransportIntegralChartRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TransportIntegralCompositionRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TransportIntegralCounitData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TransportIntegralCounitRealization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TransportIntegralStageConstruction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackTowerBounds | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackTowerDomain | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.TwistedPullbackTowerOrigins | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.UniformTowerTensorClosure | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.VectorIntegrationChartTranspose | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.VectorIntegrationIdentityAdjunct | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.VectorTraceScalarDescent | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.WeilEquivarianceOfPurityAndTrace | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Paper.WeilPurityEquivarianceData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.DncCoefficientTransportData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingExponent | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.FiniteSectionFamilyConstancy | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineChartFormulas | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineFormulaData | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.ReductionOrientation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SecSmoothPurity.SectionScalarBaseChange | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SixFunctors.AffineDualizingCoefficient | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SixFunctors.KappaCoefficientCoherence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SixFunctors.KappaGeometricComparisons | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.SixFunctors.KappaMixedCoherence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| TargetsCheck | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.SmoothPurity.Defs | E1 | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.Statement | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.GenericQuotient | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.HomologyUnit | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.Main | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.Product | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.PullbackFamily | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.TraceClass | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.WeilBaseChange | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed | Transitive consumer; declarations and mathematical data unchanged. |

## Status

landed 20261027T094354-L-219008 2026-10-27 (merge of deliver/E7/Sheaf.Paper.PurityConventions)
