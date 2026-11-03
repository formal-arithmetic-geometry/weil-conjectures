/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecialization
public import WeilConjectures.SmoothPurity.Supporting.DiagonalExchangeCube
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessTheorem
import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarRestriction
import WeilConjectures.AlgebraicGeometry.SmoothPurity.ChartNormalizedModelIdentification
import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.CompactificationRefinementCoherence
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportDomains
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
import WeilConjectures.AlgebraicGeometry.SmoothOfRelativeDimension.SmoothAdmissibleCoordinateCover
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerBinaryPairGluing
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerPairOpenRestriction2
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerLocalCounitRepresentability
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1GeometricCoordinates
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRing
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerBoundsOperations
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerBoundsOperations
import WeilConjectures.AlgebraicGeometry.SmoothPurity.TowerOperationsGroundFieldRetagging
import WeilConjectures.AlgebraicGeometry.SpFiniteOrientation.FiniteOrientationReduction
import WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLocallyFreeLineModels
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormula
import Mathlib.FieldTheory.Finite.Basic
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.SpTowerMate.SmoothPurityTowerMateEvaluationReduction
import WeilConjectures.AlgebraicGeometry.SpIntegralAdjunction.IntegralReconstructionComparisonData
import WeilConjectures.AlgebraicGeometry.IntegralReconstructionComparisons.IntegralReconstructionComparisons
import WeilConjectures.AlgebraicGeometry.Picard.SpTwistedPullback.TwistedPullbackReductionData
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedEquivalence
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionRestriction
import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
import WeilConjectures.SmoothPurity.Pur.PurReductionLimitShiftAdjunction
import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.AlgebraicGeometry.Picard.IntegralStrictReductionModel
import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceReduction
import WeilConjectures.SmoothPurity.Supporting.SignedTwistFirstReduction
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Picard.SpTwistedPullback.TwistedPullbackLineMembership
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitSupport
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitRealization
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1GeometricCoordinates
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRing
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerBoundsOperations
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormula
import Mathlib.FieldTheory.Finite.Basic
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.SpTowerMate.SmoothPurityTowerMateEvaluationReduction
import WeilConjectures.AlgebraicGeometry.SpIntegralAdjunction.IntegralReconstructionComparisonData
import WeilConjectures.AlgebraicGeometry.IntegralReconstructionComparisons.IntegralReconstructionComparisons
import WeilConjectures.AlgebraicGeometry.Picard.SpTwistedPullback.TwistedPullbackReductionData
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedEquivalence
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionRestriction
import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
import WeilConjectures.SmoothPurity.Pur.PurReductionLimitShiftAdjunction
import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.AlgebraicGeometry.Picard.IntegralStrictReductionModel
import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceReduction
import WeilConjectures.SmoothPurity.Supporting.SignedTwistFirstReduction
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Picard.SpTwistedPullback.TwistedPullbackLineMembership
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitSupport
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitRealization
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessTheorem

/-! # Finite orientation, tensor, and purity-map squares on Noetherian schemes

Source: current blueprint sk-prop-sp-purity-bc-factors, finite part
(blueprint: lem-pur-general-finite-base-change-factors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SmoothPurityBaseChange

/-- The two factors and their composite commute with pullback, without a
finite-field datum. The arrows are the prescribed exceptional exchange and
Kummer-normalized line comparison.
Source: sk-prop-sp-purity-bc-factors, finite coefficient clause
(blueprint: lem-pur-general-finite-base-change-factors).

Proof: apply the intrinsic normalized-orientation base-change theorem. The
existing tensor/counit calculation is already independent of a field; apply it
to the same pullback square. Expand gamma and use tensor-pullback naturality to
compose these two squares. Finally apply the etale/pro-etale comparison functor
to all three equations. No inverse image is required to be flat. -/
theorem finite_factors_general
    (ell : ℕ) [Fact ell.Prime]
    (X Y Y' : Scheme.{u})
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Y']
    (f : X ⟶ Y) (v : Y' ⟶ Y) (d : ℕ)
    [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    [SmoothOfRelativeDimension d f]
    [IsNoetherian (pullback f v)]
    (n : ℕ) (hn : 1 ≤ n) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ell ^ n : ℕ) : A) = 0)
    (g : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (g' : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst (pullback.snd f v) (pullback.snd f v))
      (pullback.diagonal (pullback.snd f v)))
    (hX : IsUnit ((ell ^ n : ℕ) : Γ(X, ⊤)))
    (hX' : IsUnit ((ell ^ n : ℕ) : Γ(pullback f v, ⊤)))
    (alpha : Etale.dualizingComplex A f ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA X d)
    (alpha' : Etale.dualizingComplex A
        (pullback.snd f v) ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA (pullback f v) d)
    (_ha : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA f d g hX alpha)
    (_ha' : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA (pullback.snd f v)
      d g' hX' alpha') :
    (Etale.FiniteSmoothPurity.comparison A (pullback f v)).map
        ((Etale.ordinaryFinitePullback A (pullback.fst f v)).map alpha.inv ≫
          Etale.dualizingComplexBaseChangeMap A
            (IsPullback.of_hasPullback f v)) =
      (Etale.FiniteSmoothPurity.comparison A (pullback f v)).map
        ((Etale.vectorIntegrationBaseCoefficientPullback A (ell ^ n) hA
          (PurityFiniteSetting.purityTwistTransport A (ell ^ n)
            (pow_pos (Fact.out : ell.Prime).pos n) hA)
          (pullback.fst f v) hX d).hom ≫ alpha'.inv) ∧
    ∀ K : Etale.DerivedCategoryModule A Y,
      Etale.FiniteSmoothPurity.IsCtf A Y
        ((Etale.FiniteSmoothPurity.comparison A Y).obj K) →
      (Etale.FiniteSmoothPurity.comparison A (pullback f v)).map
          ((Etale.ordinaryFinitePullback A (pullback.fst f v)).map
              (Etale.smoothTensorDualityMap A f
                (Etale.isIso_projectionMap_of_finite A f) K) ≫
            (Etale.rightDerivedUpperShriekBaseChangeMap A
              (IsPullback.of_hasPullback f v)).app K) =
        (Etale.FiniteSmoothPurity.comparison A (pullback f v)).map
          ((Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
              (pullback.fst f v)
              ((Etale.ordinaryFinitePullback A f).obj K)
              (Etale.dualizingComplex A f)).hom ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) (pullback f v)).map
              (Etale.derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
                (IsPullback.of_hasPullback f v).toCommSq K)).app _ ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) (pullback f v)).obj
              ((Etale.ordinaryFinitePullback A (pullback.snd f v)).obj
                ((Etale.ordinaryFinitePullback A v).obj K))).map
                  (Etale.dualizingComplexBaseChangeMap A
            (IsPullback.of_hasPullback f v)) ≫
            Etale.smoothTensorDualityMap A
              (pullback.snd f v)
              (Etale.isIso_projectionMap_of_finite A (pullback.snd f v))
              ((Etale.ordinaryFinitePullback A v).obj K)) ∧
      (Etale.FiniteSmoothPurity.comparison A (pullback f v)).map
          ((Etale.ordinaryFinitePullback A (pullback.fst f v)).map
              (Etale.FiniteSmoothPurity.gamma A f _ alpha K) ≫
            (Etale.rightDerivedUpperShriekBaseChangeMap A
              (IsPullback.of_hasPullback f v)).app K) =
        (Etale.FiniteSmoothPurity.comparison A (pullback f v)).map
          ((Etale.ordinaryFiniteTwistedPullbackComparison A f
              (pullback.snd f v) v (pullback.fst f v)
              (Etale.FiniteSmoothPurity.line A (ell ^ n) hA X d)
              (Etale.FiniteSmoothPurity.line A (ell ^ n) hA (pullback f v) d) K
              ((Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
                (IsPullback.of_hasPullback f v).toCommSq).symm.app K)
              (Etale.vectorIntegrationBaseCoefficientPullback A (ell ^ n) hA
                (PurityFiniteSetting.purityTwistTransport A (ell ^ n)
                  (pow_pos (Fact.out : ell.Prime).pos n) hA)
                (pullback.fst f v) hX d)).hom ≫
            Etale.FiniteSmoothPurity.gamma A (pullback.snd f v) _ alpha'
              ((Etale.ordinaryFinitePullback A v).obj K)) := by
  have ho := finite_orientation_base_change_general ell X Y Y' f v d n hn A hA
    g g' hX hX' alpha alpha' _ha _ha'
  refine ⟨congrArg (fun z ↦
    (Etale.FiniteSmoothPurity.comparison A (pullback f v)).map z) ho, ?_⟩
  intro K _hK
  have ht := tensor_base_change A (IsPullback.of_hasPullback f v) K
  refine ⟨congrArg (fun z ↦
    (Etale.FiniteSmoothPurity.comparison A (pullback f v)).map z) ht, ?_⟩
  apply congrArg (fun z ↦
    (Etale.FiniteSmoothPurity.comparison A (pullback f v)).map z)
  exact gamma_base_change A (IsPullback.of_hasPullback f v) K
    _ _ alpha alpha' _ ho ht

end AlgebraicGeometry.ProEtale.SmoothPurityBaseChange
