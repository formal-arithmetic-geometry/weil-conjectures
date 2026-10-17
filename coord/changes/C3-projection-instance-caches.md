# AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal

## Reason

The original module exceeds the 60-second single-file limit. Its concrete derived-functor
expressions repeatedly instantiate the category, transported coefficient multiplication,
abelian and monoidal structures, and graded tensor coproducts of internal modules.
The earlier attempt's three public caches in the upstream file were refused by rule 4.

This repair instead adds canonical instance caches to the existing, unclaimed
`Sheaf.Paper.IntegralResidueDerivedMonoidal` module. This module is already in the public
import closure of the item's original imports. An explicit private import makes the new
names available to the proof elaborator. All data caches are exactly the existing instances;
all property caches are proved with `inferInstance`. The item registers them only locally.
There are no new global instances, assumptions, or mathematical constructions.

All existing upstream signatures, attributes, public imports and non-theorem data bodies
are verbatim. The item changes only three original theorem proofs, adds proved private
helpers, and selects the caches locally. In particular every original literal
`L((f)^*⟦Λ⟧)` expression is preserved. The previous `projectionUpperStar` and
`projectionUpperStarMonoidal` aliases are absent.

## Old

There were no declarations in the appended cache block below. Every existing declaration
of `Sheaf.Paper.IntegralResidueDerivedMonoidal` is unchanged, including its data bodies.
The item had five original holes and no local cache registrations.

## New

The Sheaf module now contains only the following canonical cache declarations (all are
proved by `inferInstance` and are registered only locally by the item):

- `AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal`;
- `AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian`;
- `AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal`;
- `AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived`;
- `AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal`;
- `AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj`;
- `AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory`.

The duplicate `CategoryTheory.ProjectionCache.scalar*` declarations from the returned
attempt were removed. The existing `CondensedFlatCoefficientCalculus` module already
states those properties, but its declarations are private and cannot be imported by name;
the repaired proof therefore relies on ordinary instance synthesis for those properties.
No upstream signature, public import, or non-theorem data body changes.

## Users

The table includes every module returned by `tools/downstream.py` for the changed Sheaf
module. No prior user refers to the new names. Existing exported instances and declarations
of that module are unchanged; the cache registrations occur only in the item.
No target statement or definition's mathematical meaning changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueDerivedMonoidal | unclaimed | Add canonical caches; all existing declarations are unchanged. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueOrdinaryTensorNormalization | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueProjectionNormalization | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueScalarCounitModel | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueScalarRouteModel | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorPullCounitCore | A3 | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorPullCounitModel | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | B4 | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| TargetsCheck | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | B3 | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | C3 | Select the caches locally and prove three naturality holes. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | B2 | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Existing declarations and instances are unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Existing declarations and instances are unchanged; no adaptation. |

## Status

landed 20261017T190421-L-2538885 2026-10-17 (merge of deliver/C3/WeilConjectures.PoincareDuality.ProjectionFormula)
