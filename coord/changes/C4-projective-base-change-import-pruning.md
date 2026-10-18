# AlgebraicGeometry.projective_base_change import pruning

## Reason

The proof uses only the projectivity definitions, the projective-space lift API,
and Mathlib pullbacks and base-change instances. The former imports of
`Curve.SmoothProjective`, `Modules.VeryAmple`, and both base-change convention
modules are unnecessary. Publicly import the canonical lower module that defines
`IsProjective`, as used by the unchanged theorem signature. This removes broad
re-exports; no declaration signature, visibility, definition, or target meaning changes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
--uses AlgebraicGeometry.projective_base_change` reports the transitive importers
listed below. All six direct consumers import this module privately for proofs;
their public interfaces therefore do not re-export its former public imports.
They already import the projectivity definitions or smooth-projective curve API
required by their statements independently. Each unchanged direct consumer is
compiled against the reduced module in this sandbox. No other module is edited.
Holders are the available claim records at preparation time.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | H5 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | U2 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | M3 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | C6 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldCurveCompletionInsep | S8 | Direct proof-only importer; existing signatures unchanged; compile checked. |
| Sheaf.AlgebraicGeometry.FiniteGenericCurveModel | P9 | Direct proof-only importer; existing signatures unchanged; compile checked. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | X2 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | H3 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.GenusWellDefined | unclaimed | Direct proof-only importer; existing signatures unchanged; compile checked. |
| Sheaf.AlgebraicGeometry.GoodCurvesGenericDiagram | Q5 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | D9 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | X3 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | B4 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | N4 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveCoordinateBoundary | R3 | Direct proof-only importer; existing signatures unchanged; compile checked. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveConstant | J5 | Direct proof-only importer; existing signatures unchanged; compile checked. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup | E9 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveGenericallyFinite | T5 | Direct proof-only importer; existing signatures unchanged; compile checked. |
| Sheaf.AlgebraicGeometry.ProjectiveLineConstructible | V3 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages | F3 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.PoincareDuality.CompatibleIntegralRootBases | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.PoincareDuality.CompatiblePrimitiveRoots | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.PoincareDuality.IntegralResidueLimit | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.PoincareDuality.IntegralResidueQuotient | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.PoincareDuality.IntegralTateBasis | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.PoincareDuality.IntegralTateLocalLine | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.PoincareDuality.TateTwistOneLocalLine | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| TargetsCheck | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | B3 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | B2 | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.Statement | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Exported environment unchanged through proof-only direct importers; no adaptation. |

## Status

landed 20261018T062715-L-636731 2026-10-18 (merge of deliver/C4/Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange)
