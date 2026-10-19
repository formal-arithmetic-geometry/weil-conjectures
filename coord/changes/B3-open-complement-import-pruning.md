# Sheaf.Paper.OpenComplementUnconditional import visibility

## Reason

The original header publicly exported several proof-plan dependencies unused by the completed proofs. Prune them and keep proof dependencies private to the module. No declaration signature, definition, instance, or attribute changes. The theorem statements still use only the retained public imports. The library already imports the predicate and coefficient interfaces explicitly.

## Old

```lean
public import Sheaf.AlgebraicGeometry.OpenComplementCondition
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral
import Sheaf.AlgebraicGeometry.DirectImageFinitenessInputHolds
import Sheaf.AlgebraicGeometry.DirectImageFinitenessInput
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Sheaf.AlgebraicGeometry.OpenComplementKnown
import Sheaf.Paper.FiniteFieldFiber
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
```

## New

```lean
public import Sheaf.AlgebraicGeometry.OpenComplementCondition
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.AlgebraicGeometry.DirectImageFinitenessInputHolds
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.RingTheory.KrullDimension.Polynomial
```

## Users

The following is the complete transitive import list from tools/downstream.py. The three direct importers use private imports of this item; validation results are appended below. Downstream theorem statements retain the same meaning, because the four theorem signatures and every definition used by them are identical. Consumers require no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicMiddleExtensionConstructible | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicPurityFiniteTensor | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicPurityObjects | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicPurityRootComparisons | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicPuritySourceReduction | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicPurityTwistReduction | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicSectionClosedSupport | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AffineSpaceRationalInduction | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ArithmeticRoots | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.BasicOperationsCoefficientReduction | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.BoundaryDualizingComposition | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.BoundaryQMaps | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.BoundaryQTransport | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.BrownExceptionalAdjoint | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CartierClassAgreement | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ChernFlagFormula | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CommonStageConstituentNonexceptional | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CompactSupportCondensedRealization | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CompactificationCoherenceCocycle | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CompactificationLocalizing | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CompactificationRefinementLocalizing | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.DlConstantFieldCharts | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ExceptionalFiniteRealization | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ExceptionalProEtaleRealization | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ExceptionalSiteRealization | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteCoefficientHomChange | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteConstructibleHom | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteProperLocalizing | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteReductionAffineOrientation | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteReductionChartCalculus | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteReductionComparisons | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteReductionRootCharts | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteSmoothPullbackExchange | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteStageVerdierBiduality | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FiniteTorStability | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FourierTraceFormula | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.IntegralConstructibleInternalHom | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.IntegralDirectImageTower | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.IntegralExceptionalInverseImage | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.IntegralOpenImageProperFormulas | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.IntegralProperBaseChange | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.IntegralProperDirectSums | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.InterchangeProperPasting | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.InternalHomPullback | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.IteratedWeilMap | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.LocalFrobeniusConjugacy | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.LocalizedTopChern | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.LocalizingLowerShriekComposition | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.MateOpenRestriction | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.MiddleExtensionHcZero | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProEtaleProperOpenInterchange | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProperBaseChangeRational | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProperCoincidenceFrobenius | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProperHeartBound | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProperSectionsSemilinearGerms | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurAdicReconstruction | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityAffineChartBounds | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityAffineLineOrientation | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityChernClasses | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityCoprojection | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityDiagonalDualizingObject | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityDivisorClass | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityDncComparisons | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityDncFamilyIntrinsic | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityDncInvariance | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityGysinStructure | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.RationalLocalizingProjectionFormula | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.RationalSmoothPurityCanonical | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.RationalStalkExact | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.RestrictionLocal | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.SfBidualityClass | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.SfPreservationClass | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.SfProEtaleProjectionFormula | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.SmoothMateCounitCancellation | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.SmoothPurityMap | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.SmoothTrace | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TensorTraceTranspose | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TraceCompactificationCohomology | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TraceFixedScheme | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TraceTransposeBaseChange | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TwConventions | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.TwistFrobeniusScalar | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.VerdierExchange | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.WeilFourierInversion | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.WeilOne | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.WeilOpenImageDelta | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.WeilPullbackLocalFrobenius | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.WfTensorCompletionFrobenius | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ZlFiniteAdicDirectImage | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Paper.ZlShriekComposition | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SecSmoothPurity.ReductionDirectImage | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SecSmoothPurity.ReductionExceptional | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.BoundaryDualityDischarge | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.FiniteDualizing | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.FrobeniusFixedPoints | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.GeneratorReductionStatement | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.IntegralVerdier | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.ProperImageLocalizingProper | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.RationalOperations | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.RationalVerdier | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Targets.PoincareUncurry | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| TargetsCheck | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.SmoothPurity.Defs | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.Statement | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.TraceFormula.Basic | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.TraceFormula.Statement | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.AffineLineCohomology | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.Curve | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.Examples | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.TraceFormula | claimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |
| WeilConjectures.ZetaFunction.Weights | unclaimed | no declaration type or definition changes; only unused reexports removed; no source adaptation |

Validation: the delivered module compiled without warnings. The direct consumers Sheaf.Paper.FiniteCoefficientHomChange (10.0 seconds) and Sheaf.Paper.PurityAffineChartBounds (5.5 seconds) compiled against the delivered module. Sheaf.Paper.FiniteTorStability could not be checked: three attempts (including the resumed-session retry) stopped at its imports with missing shared artifact WeilConjectures.Compactification.RefinementCategory.olean, before elaborating any declaration. No consumer source was changed.

## Status

landed 20261019T093252-L-2287286 2026-10-19 (merge of deliver/B3/Sheaf.Paper.OpenComplementUnconditional)
