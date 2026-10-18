# AlgebraicGeometry.Etale.rightDerivedLowerStar_preservesCoproducts_of_finite_dimension

## Reason

Prune unused proof dependencies after proving the theorem from the existing source-library
finite-cohomological-dimension criterion. Replace broad public imports by direct public imports
needed to elaborate the unchanged statement. Public import removal is an interface change even
though no declaration, instance, definition, universe or hypothesis is changed in this delivery.
All other newly added imports are private proof imports. No consumer is adapted.

The exact original theorem signature is preserved:

```lean
theorem rightDerivedLowerStar_preservesCoproducts_of_finite_dimension
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (f : U ⟶ T) [QuasiCompact f] [QuasiSeparated f]
    (c : ℕ)
    (hc : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (p : ℕ),
      c < p → IsZero (((lowerStar (ModuleCat.{u + 1} A) f).rightDerived p).obj M)) :
    ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) f)
```

## Old

Original complete import block, verbatim:

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
```

## New

Replacement complete import block, verbatim:

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.LiftToFinset
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import all Sheaf.CategoryTheory.CompactTestsRightAdjointCoproducts
```

## Users

`tools/downstream.py` reports 390 transitive consumers. Its `--uses` check for
`rightDerivedLowerStar_preservesCoproducts_of_finite_dimension` finds no consumer mentioning
the declaration yet. The direct importers are
`Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality` and
`Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts`.
`tools/import_prune_check.py` passes: no downstream use of a declaration lost through these
removed imports was found. This is the prescribed static consumer check, not a global build;
the maintainer's independent global build verifies the delivery. No consumer's statement or
proof is modified. The group column is deliberately not queried for untouched consumers;
there is no cross-group adaptation or claim in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.OpenDirectImageOverField` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.SmoothGenericDirectImage` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.AlgebraicGeometry.SmoothTensorDuality` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.CategoryTheory.ThreeStepAdjunctionComparison` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.BoundedExchangeAmbient` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CoefficientDerivedFunctorAPI` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CoefficientExchangeFromComparisons` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedClosedCostalkDerivedContinuity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedConstructibleExtensionTower` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedConstructibleOneStep` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedConstructibleOpenClosedImages` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedFiniteCoefficientLocalization` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedFiniteFamilyHomDescent` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedFiniteLocalSubmodules` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedFiniteModelExtensions` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedFiniteModelProofAPI` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedLfpCoefficientModel` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedLfpHomContinuity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedLocalModelGluing` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedLocalPieceCostalkModel` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedLocalPieceHomContinuity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedLocallyClosedExtensionTower` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedLocallyClosedOneStep` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedOpenClosedRecollement` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarCoefficientConstruction` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarComparisons` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarExchangeLeftAdjunct` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarExchangeRightAdjunct` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarFieldCoefficientSquare` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarFieldEvaluationLinearity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarFieldFiberExtension` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarFieldPointCoefficientValue` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarFunctionCoefficients` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarFunctionPresentations` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarLfpLocalTriviality` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarLfpMatrixRefinement` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarPullbackCube` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedQbarScalarPullback` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedStratumModelAssembly` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedStratumModelInductionStep` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedStratumModelInductionStepEmpty` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonempty` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ConstructibleCokernelsExtensions` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousAffineEtaleLattice` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousChartSchemeNaturality` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousCoefficientModuleEncoding` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousCoefficientRealizations` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousConstructibleIntegralDenominators` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousConstructibleIntegralGluing` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousConstructibleIntegralImage` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousConstructibleIntegralModel` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousConstructibleIntegralSingle` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousConstructibleIntegralStratum` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousConstructibleIntegralTransport` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousEtaleLocalLattices` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousExchangeIntegralModel` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousFiniteFreeDenominators` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousFiniteFreeKernelModel` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralComparisons` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralComplexTelescope` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralExchangeEquality` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralExchangeSquare` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralLocalization` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralLocalizationContinuity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralLocalizationCounit` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralLocalizationHomology` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralLocalizationLegs` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralLocalizationMate` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralLocalizationModel` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralModuleTelescope` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralPullComposition` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralPushComparison` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralRegularTelescope` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousIntegralUnderivedPushComparison` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousLatticeFiniteCoproduct` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousLatticeIntersectionLocalModel` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousLatticeIntersectionRationalModel` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousLatticeIntersectionRationalization` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousLatticeIntersectionSplitData` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousLatticeIntersectionSplitModel` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousLisseCoefficientDescent` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousLissePullbackSystem` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousLisseStratifiedLattices` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousLisseStratumDescent` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousLocallyFreePullback` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousModuleEncodingLattices` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousModuleEncodingLocalFreeness` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousModuleEncodingRestriction` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousModuleEncodingScalarExtension` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousModuleEncodingSliceFreeness` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.ContinuousRegularFunctions` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteCoefficientEncoding` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteCoefficientExchange` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteCoefficientRestriction` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteConstructibleEncoding` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteDerivedCoefficientData` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteEncodedPresentation` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteExchangeComparison` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteExchangeRealization` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteRealizationFunctor` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteDiscreteRestrictionEncoding` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.FiniteEtaleLocallyFreeModels` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralConstructibleKernels` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralConstructibleNakayama` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralConstructibleSequentialHom` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralConstructibleSerre` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralConstructibleSheafHom` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralExchangeReduction` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralFiniteExchangeComparison` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralFiniteFreeContractive` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralLfpEventualFreeImage` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralLfpFiniteQuotientCharts` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralLfpHomContinuity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralLfpLocalTorsionCharts` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralLfpLocallyFreeResolution` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralMatrixAnalyticCover` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralMatrixAnalyticData` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralMatrixCoefficientTransport` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralMatrixEntryProperties` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralMatrixFunctionsPullback` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralMatrixKernelLocallyFree` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralMatrixPivotCover` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralMatrixPointwiseRank` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralMatrixZeroNeighborhood` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralReductionConservative` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralReductionConstructible` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralRegularCoefficientPullback` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralRegularRationalUnit` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralResidueExchange` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralResidueExchangeAlgebra` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.Paper.IntegralScalarContractive` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.PoincareDuality.CompatibleIntegralRootBases` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.PoincareDuality.CompatiblePrimitiveRoots` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.PoincareDuality.IntegralResidueLimit` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.PoincareDuality.IntegralResidueQuotient` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.PoincareDuality.IntegralTateBasis` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.PoincareDuality.IntegralTateLocalLine` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.PoincareDuality.TateTwistOneLocalLine` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.SmoothPurity.NormalizedWitness` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.WeilSheaf.AffineCurveRangePositive` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.WeilSheaf.CohomologyGeometricConjugacy` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.WeilSheaf.CohomologyGeometricEquivalence` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `Sheaf.WeilSheaf.FiniteBoundaryPositive` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `TargetsCheck` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.Defs` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.DenseOpen` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.DeligneLaumon.Reduction.Weights` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.FourierTransform.Perverse` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.PoincareDuality.Poincare` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.PoincareDuality.Verdier` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.Etale.Derived.RationalStage` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.Localization` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.SmoothPurity.Defs` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.Statement` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.TraceFormula.Basic` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.TraceFormula.Slop.Basic` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.TraceFormula.Slop.Main` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.TraceFormula.Statement` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilObject.BoundedConstructible.Defs` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilObject.BoundedConstructible.TensorHom` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.ArtinSchreierDual` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.ArtinSchreierFrobenius` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.ArtinSchreierPurity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.ArtinSchreierTrace` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.BoundaryStalk` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.Cohomology` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.CohomologyExact` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.CohomologyShift` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.ComplexWeights` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.ConstantTwistCohomology` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.Curve` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.Defs` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.DenseOpen` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.DirectImageRestriction` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.DirectImageStalk` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.ExtensionByZero` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FiniteEtaleLisse` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.Finiteness` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.Fourier` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierInversion` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierInversion.Defs` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierInversion.TensorLisse` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierInversion.UpperStar` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierPlancherel` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierTateTwist` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierTateTwist.Transform` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierTrace` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.FourierTraceAux` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.GeometricCoinvariants` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.GeometricallyConstant` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.HomologyShift` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.LFunction` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.Localization` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.LocalizationRational` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.LowerShriek` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.LowerStar` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.LowerStarComp` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.LowerStarId` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.LowerStarPairing` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.LowerStarTensorPow` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.MiddleExtension` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.OpenImmersion` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.OpenImmersionRestriction` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.Operations` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.PoincareDuality` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.ProperCohomology` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.RealPurity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.Realizable` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.StalkConstantTwist` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.StalkExtensionByZero` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.StalkInternalHom` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.StalkOpenImmersion` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.StalkTateTwist` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.StalkTensor` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.TateTwist` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.TateTwistCohomology` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.Tensor` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.TensorObjPairing` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.TensorPower` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.TraceFunctionCongr` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.TraceFunctionOps` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.TraceFunctionTensor` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.TraceSeries` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.WeilSheaf.UpperStarPointwise` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.Examples` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.HasseWeil` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.Rationality` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.RelativePurity` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.SmoothProper` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.TraceFormula` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | not queried; untouched | No declaration or statement change; import-pruning check passes. |
| `WeilConjectures.ZetaFunction.Weights` | not queried; untouched | No declaration or statement change; import-pruning check passes. |

## Status

landed 20261018T062819-L-659082 2026-10-18 (merge of deliver/K1/Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectImageCoproducts)
