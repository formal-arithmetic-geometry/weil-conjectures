# AlgebraicGeometry.Etale.properOpenSectionGeometry

## Reason

Prove the geometry directly from Mathlib, including the closed image of the section.
The coproduct assertion of `open_section_clopen` is stronger than needed, and its
module need not be publicly re-exported. Three additional proof imports are unused.
No declaration signature or definition body changes. No target meaning changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.OpenSectionClopen
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
```

The geometry theorem had proof `by sorry`.

## New

```lean
import Mathlib.AlgebraicGeometry.Morphisms.Separated
```

The geometry theorem is proved using projection identities, `IsOpenImmersion.of_comp`,
`IsClosedImmersion.of_comp`, and `IsPullback.of_horiz_isIso_mono`.
All four existing declaration signatures and the three definition bodies are identical.

## Users

The following are all downstream modules reported by `tools/downstream.py`.
A whole-library search finds no use of `open_section_clopen` outside its own module.
`ProperOpenSection` already imports `OpenSectionClopen` directly. The six direct
importers were compiled unchanged against the modified module as a consumer check.
No other module is edited, so claim ownership is immaterial for those rows.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion | not queried (not edited) | Direct importer; compiled unchanged against the pruned imports. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons | not queried (not edited) | Direct importer; compiled unchanged against the pruned imports. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition | not queried (not edited) | Direct importer; compiled unchanged against the pruned imports. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonIso | not queried (not edited) | Direct importer; compiled unchanged against the pruned imports. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | not queried (not edited) | Direct importer; compiled unchanged against the pruned imports. |
| Sheaf.AlgebraicGeometry.ProperOpenSection | not queried (not edited) | Direct importer; compiled unchanged against the pruned imports. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.BoundedExchangeAmbient | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedCoefficientComparisons | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedConstructibleOneStep | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedFiniteModelExtensions | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedFinitePresentationDescent | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedLfpCoefficientModel | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedLfpHomContinuity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedLocalModelGluing | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedOpenClosedRecollement | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarComparisons | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarExchangeEquality | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarPullbackCube | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedQbarScalarPullback | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedSheafExtContinuity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelAssembly | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelInductionStep | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousCoefficientRealizations | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralComparisons | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalization | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralPullComposition | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralPushComparison | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousLissePullbackSystem | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousLisseStratumDescent | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousLocallyFreePullback | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.ContinuousRegularFunctions | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleKernels | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleNakayama | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleSerre | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleSheafHom | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralExchangeReduction | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralFiniteFreeContractive | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralLfpHomContinuity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralMatrixAnalyticData | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralMatrixEntryProperties | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralMatrixPivotCover | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralReductionConservative | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralReductionConstructible | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralRegularRationalUnit | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralResidueExchange | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.Paper.IntegralScalarContractive | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.PoincareDuality.CompatibleIntegralRootBases | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.PoincareDuality.CompatiblePrimitiveRoots | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.PoincareDuality.IntegralResidueLimit | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.PoincareDuality.IntegralResidueQuotient | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.PoincareDuality.IntegralTateBasis | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.PoincareDuality.IntegralTateLocalLine | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.PoincareDuality.TateTwistOneLocalLine | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.SmoothPurity.NormalizedWitness | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| TargetsCheck | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.FourierTransform.Perverse | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.PoincareDuality.Poincare | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.PoincareDuality.ProjectionFormula | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.PoincareDuality.Verdier | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.SmoothPurity.Defs | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.Statement | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.TraceFormula.Basic | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Basic | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Correspondence | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Dualizing | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Frobenius | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Main | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Stalk | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.TraceFormula.Statement | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.BoundaryStalk | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.Cohomology | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.CohomologyExact | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.CohomologyShift | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.ComplexWeights | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.Curve | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.CurveEndpoints | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.Defs | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.DenseOpen | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.DirectImageStalk | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.ExtensionByZero | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.Finiteness | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.Fourier | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierPlancherel | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierTateTwist | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierTrace | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierTraceAux | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.HomologyShift | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.LFunction | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.Localization | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.LocalizationRational | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerShriek | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerStar | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerStarComp | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerStarId | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerStarPairing | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.MiddleExtension | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.OpenImmersion | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.Operations | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.PoincareDuality | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.ProperCohomology | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.RealPurity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.Realizable | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.StalkInternalHom | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.StalkTateTwist | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.StalkTensor | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.TateTwist | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.Tensor | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.TensorObjPairing | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.TensorPower | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.TraceSeries | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.Examples | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.FinalTheorems | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.HasseWeil | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.IntegralFactors | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.Rationality | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.RelativePurity | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.SmoothProper | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.TraceFormula | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.WeightSeparation | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |
| WeilConjectures.ZetaFunction.Weights | not queried (not edited) | Transitive importer; no removed declaration is used, no adaptation needed. |

## Status

landed 20261018T062742-L-647138 2026-10-18 (merge of deliver/F1/Sheaf.AlgebraicGeometry.ProperOpenComparison)
