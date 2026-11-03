/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
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
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
import WeilConjectures.AlgebraicGeometry.SmoothOfRelativeDimension.SmoothAdmissibleCoordinateCover
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerBinaryPairGluing
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerPairOpenRestriction2
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerLocalCounitRepresentability
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1GeometricCoordinates
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRing
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerBoundsOperations
public import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.SmoothPurity.TowerOperationsGroundFieldRetagging
import WeilConjectures.AlgebraicGeometry.SpFiniteOrientation.FiniteOrientationReduction
import WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLocallyFreeLineModels
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormula
public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SpTowerMate.SmoothPurityTowerMateEvaluationReduction
public import WeilConjectures.AlgebraicGeometry.SpIntegralAdjunction.IntegralReconstructionComparisonData
public import WeilConjectures.AlgebraicGeometry.IntegralReconstructionComparisons.IntegralReconstructionComparisons
public import WeilConjectures.AlgebraicGeometry.Picard.SpTwistedPullback.TwistedPullbackReductionData
public import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedEquivalence
public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionRestriction
public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
public import WeilConjectures.SmoothPurity.Pur.PurReductionLimitShiftAdjunction
public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import WeilConjectures.AlgebraicGeometry.Picard.IntegralStrictReductionModel
public import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceReduction
public import WeilConjectures.SmoothPurity.Supporting.SignedTwistFirstReduction
public import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
public import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Picard.SpTwistedPullback.TwistedPullbackLineMembership
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitSupport
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitRealization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound

import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
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
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
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
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecialization
import all WeilConjectures.SmoothPurity.Supporting.DiagonalExchangeCube
import all WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessTheorem

/-! # Smooth-purity base-change factors over the standing field

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-trace/sec-base-change-and-composition/
sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.md, (1), (2), consequence
(blueprint: det-sp-purity-bc-factors).

The previously published factor statements use a finite-field datum. These statements
retain their concrete canonical maps and allow finite or algebraically closed fields,
including characteristic zero. The tower inputs need not be normalized.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SmoothPurityBaseChange

open Etale Etale.FiniteSmoothPurity
open scoped CategoryTheory.Functor

private theorem diagonal_factor_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Y']
    (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    (v : Y' ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f]
    [IsNoetherian (pullback f v)]
    [HasInvertibleExponent A X] [HasInvertibleExponent A (pullback f v)] :
    (Etale.upperStar (ModuleCat.{u + 1} A)
      (pullback.fst f v)).leftDerivedFunctor.map (finiteSmoothDiagonalFactor A f) ≫
        NoetherianSectionSpecialization.sectionMap A (pullback.fst f f)
          (pullback.fst (pullback.snd f v) (pullback.snd f v))
          (pullback.fst f v) (diagonalCubeMap f v) (cube_projection_squares f v).1
          (pullback.diagonal f) (pullback.diagonal (pullback.snd f v)) (cube_diagonal f v) =
      Etale.dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f v) ≫
        finiteSmoothDiagonalFactor A (pullback.snd f v) := by
  obtain ⟨sq₁, sq₂⟩ := cube_projection_squares f v
  have hΔ := cube_diagonal f v
  have : HasInvertibleExponent A (pullback f f) :=
    HasInvertibleExponent.of_hom (show pullback f f ⟶ X from pullback.fst f f)
  have hIso {B C B' C' : Scheme.{u}} {g : B ⟶ C} {g' : B' ⟶ C'}
      {a : B' ⟶ B} {b : C' ⟶ C}
      [QuasiSeparatedSpace C] [HasInvertibleExponent A B]
      [HasCompactification g] [HasCompactification g'] [QuasiCompact g']
      [SmoothOfRelativeDimension d g] (sq : IsPullback a g' g b) :
      IsIso (Etale.dualizingComplexBaseChangeMap A sq) := by
    have := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension A g d sq
    exact (Etale.isIso_dualizingComplexBaseChangeMap_iff A sq).2 inferInstance
  have := hIso (IsPullback.of_hasPullback f f).flip
  have := hIso
    (IsPullback.of_hasPullback (pullback.snd f v) (pullback.snd f v)).flip
  have := hIso sq₁
  have := hIso (IsPullback.of_hasPullback f v)
  let b := asIso (Etale.dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f f).flip)
  let b' := asIso (Etale.dualizingComplexBaseChangeMap A
    (IsPullback.of_hasPullback (pullback.snd f v) (pullback.snd f v)).flip)
  let bp := asIso (Etale.dualizingComplexBaseChangeMap A sq₁)
  let e := asIso (Etale.dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f v))
  have hpaste := cube_dualizing_base_comp A (IsPullback.of_hasPullback f f).flip sq₁
  have hpaste' := cube_dualizing_base_comp_chosen A
    (IsPullback.of_hasPullback f v)
    (IsPullback.of_hasPullback (pullback.snd f v) (pullback.snd f v)).flip
    (diagonalCubeMap f v ≫ pullback.snd f f) (pullback.fst f v ≫ f)
    sq₂.w (pullback.condition (f := f) (g := v))
    (sq₁.paste_horiz (IsPullback.of_hasPullback f f).flip)
  have heq :
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (diagonalCubeMap f v)).leftDerivedFunctor.map b.hom ≫ bp.hom =
      (diagonalCubePullbackIso A (diagonalCubeMap f v) (pullback.snd f f)
        (pullback.snd (pullback.snd f v) (pullback.snd f v))
        (pullback.fst f v) sq₂.w).hom.app _ ≫
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (pullback.snd (pullback.snd f v) (pullback.snd f v))).leftDerivedFunctor.map e.hom ≫
        b'.hom := by
    have h := hpaste.symm.trans hpaste'
    apply (cancel_epi ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (diagonalCubeMap f v) (pullback.snd f f)).hom.app _)).mp
    simpa only [diagonalCubePullbackIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc, Iso.hom_inv_id_app_assoc, b, b', bp, e, asIso_hom] using h
  let k := (Etale.upperStar (ModuleCat.{u + 1} A)
    (pullback.diagonal f)).leftDerivedFunctor.mapIso b.symm ≪≫
    (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f)).app _
  let k' :=
    (Etale.upperStar (ModuleCat.{u + 1} A)
      (pullback.diagonal (pullback.snd f v))).leftDerivedFunctor.mapIso b'.symm ≪≫
    (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (pullback.diagonal (pullback.snd f v))
      (pullback.snd (pullback.snd f v) (pullback.snd f v))
      (pullback.diagonal_snd (pullback.snd f v))).app _
  have hk := cube_section_equation A
    (pullback.fst f v) (pullback.snd f f)
    (pullback.snd (pullback.snd f v) (pullback.snd f v)) (diagonalCubeMap f v)
    (pullback.diagonal f) (pullback.diagonal (pullback.snd f v)) sq₂.w hΔ
    (pullback.diagonal_snd f) (pullback.diagonal_snd (pullback.snd f v))
    _ _ _ _ b b' bp e heq
  rw [← Category.assoc] at hk
  change _ ≫ k'.hom =
    (Etale.upperStar (ModuleCat.{u + 1} A)
      (pullback.fst f v)).leftDerivedFunctor.map k.hom ≫ e.hom at hk
  have hsection :
      NoetherianSectionSpecialization.sectionMap A (pullback.fst f f)
        (pullback.fst (pullback.snd f v) (pullback.snd f v))
        (pullback.fst f v) (diagonalCubeMap f v) (cube_projection_squares f v).1
        (pullback.diagonal f) (pullback.diagonal (pullback.snd f v)) (cube_diagonal f v) ≫
          k'.hom =
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (pullback.fst f v)).leftDerivedFunctor.map k.hom ≫ e.hom := by
    simpa only [NoetherianSectionSpecialization.sectionMap, diagonalCubePullbackIso,
      Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
      Category.assoc, bp, asIso_hom,
      sectionInvariant] using hk
  have hD : finiteSmoothDiagonalFactor A f = k.inv := rfl
  have hD' : finiteSmoothDiagonalFactor A (pullback.snd f v) = k'.inv := rfl
  rw [hD, hD']
  apply (cancel_mono k'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (Etale.upperStar (ModuleCat.{u + 1} A) (pullback.fst f v)).leftDerivedFunctor.map k.inv ≫
    (_ ≫ k'.hom) = _
  rw [hsection, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The inverse diagonal orientation commutes with arbitrary change of base.
This is only the coefficient-line factor; it says nothing about tensor mates or gamma.
Source: latest blueprint sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-factors.proof.md, proof (1)
(blueprint: det-sp-purity-bc-factors).

Proof: first work at R = Z/ell^n. The diagonal exchange cube identifies the
restriction of the projection exchange with the unit exceptional exchange.
The section DNC/integration base-change square identifies the pulled-back
normalized Rees specialization and the normal-bundle integration factor.
Compose these squares. The diagonal specialization of the integrated DNC
comparison is the specified diagonal orientation, so Pi_f' e_R = u*Pi_f.

For A, use the unital map R -> A. Finite general-ring purity identifies its
direct diagonal orientation with scalar extension of Pi_f. The mixed
coefficient/exceptional-exchange square and finite scalar orientation transport
then give Pi_f',A e_A = u*Pi_f,A. The supplied OrientationNormalized equations
fix the same arrows: uniqueness of the Rees comparison normalized at one
identifies the specialization, and cancellation of the invertible bundle
integration adjunct identifies alpha and alpha'. Geometry consists entirely
of proofs, so its supplied witnesses do not alter any arrow. These arguments
apply in the ordinary etale presentation; alternatively its bounded-below site
comparison is fully faithful on the smooth dualizing objects and Tate lines.
Compose with u*(alpha inverse) and alpha' inverse to obtain the displayed
inverse equation. Unit and root comparisons are the specified Kummer-normalized
ones. Zero rank uses empty tensor products and the unit comparison; empty
schemes and the zero coefficient ring give the same equations in zero categories.
No flatness of A over R, or of v, is needed. -/
private theorem finite_orientation_base_change_field
    (k : Type u) [Field k] (ell : ℕ) [Fact ell.Prime]
    (X Y Y' : Over (Spec (.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (d : ℕ)
    [IsSeparated f.left] [QuasiCompact f.left] [HasCompactification f.left]
    [SmoothOfRelativeDimension d f.left]
    [IsNoetherian (pullback f.left v.left)]
    (n : ℕ) (hn : 1 ≤ n) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ell ^ n : ℕ) : A) = 0)
    (g : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f.left f.left) (pullback.diagonal f.left))
    (g' : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst (pullback.snd f.left v.left) (pullback.snd f.left v.left))
      (pullback.diagonal (pullback.snd f.left v.left)))
    (hX : IsUnit ((ell ^ n : ℕ) : Γ(X.left, ⊤)))
    (hX' : IsUnit ((ell ^ n : ℕ) : Γ(pullback f.left v.left, ⊤)))
    (alpha : Etale.dualizingComplex A f.left ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA X.left d)
    (alpha' : Etale.dualizingComplex A
        (pullback.snd f.left v.left) ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA (pullback f.left v.left) d)
    (_ha : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA f.left d g hX alpha)
    (_ha' : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA (pullback.snd f.left v.left)
      d g' hX' alpha') :
    (Etale.ordinaryFinitePullback A (pullback.fst f.left v.left)).map alpha.inv ≫
        Etale.dualizingComplexBaseChangeMap A
          (IsPullback.of_hasPullback f.left v.left) =
      (Etale.vectorIntegrationBaseCoefficientPullback A (ell ^ n) hA
        (PurityFiniteSetting.purityTwistTransport A (ell ^ n)
          (pow_pos (Fact.out : ell.Prime).pos n) hA)
        (pullback.fst f.left v.left) hX d).hom ≫ alpha'.inv := by
  have _ := hn
  let := g
  let := g'
  have hY'loc : IsLocallyNoetherian Y'.left :=
    LocallyOfFiniteType.isLocallyNoetherian Y'.hom
  have hY'compact : CompactSpace Y'.left :=
    QuasiCompact.compactSpace_of_compactSpace Y'.hom
  have : IsNoetherian Y'.left := {}
  let N := ell ^ n
  have hN : 0 < N := pow_pos (Fact.out : ell.Prime).pos n
  have : HasInvertibleExponent A X.left := ⟨N, hN, hA, hX⟩
  have : HasInvertibleExponent A (pullback f.left v.left) := ⟨N, hN, hA, hX'⟩
  obtain ⟨κ, hκ, sq, heq⟩ := _ha
  obtain ⟨κ', hκ', sq', heq'⟩ := _ha'
  let ψ := integratedSpecialization A d (pullback.fst f.left f.left)
    (pullback.diagonal f.left) (pullback.diagonal_fst f.left) sq N hN hA hX κ
  let ψ' := integratedSpecialization A d
    (pullback.fst (pullback.snd f.left v.left) (pullback.snd f.left v.left))
    (pullback.diagonal (pullback.snd f.left v.left))
    (pullback.diagonal_fst (pullback.snd f.left v.left)) sq' N hN hA hX' κ'
  have halpha : alpha.hom = finiteSmoothDiagonalFactor A f.left ≫ ψ := by
    let := normalSectionMap_isIso A d (pullback.fst f.left f.left)
      (pullback.diagonal f.left) (pullback.diagonal_fst f.left) sq N hN hA hX
    let := (Etale.FiniteRingSectionDeformation.bundleAdjoint_isIso N hN A hA
      X.left hX d (ConormalGradedAlgebra.piece (pullback.diagonal f.left) 1)).2
    apply (cancel_mono (Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
      N hN A hA X.left hX d
      (ConormalGradedAlgebra.piece (pullback.diagonal f.left) 1) ≫
      normalSectionMap A d (pullback.fst f.left f.left) (pullback.diagonal f.left)
        (pullback.diagonal_fst f.left) sq)).mp
    rw [Category.assoc, integratedSpecialization_normalization]
    exact heq.symm
  have halpha' : alpha'.hom =
      finiteSmoothDiagonalFactor A (pullback.snd f.left v.left) ≫ ψ' := by
    let := normalSectionMap_isIso A d
      (pullback.fst (pullback.snd f.left v.left) (pullback.snd f.left v.left))
      (pullback.diagonal (pullback.snd f.left v.left))
      (pullback.diagonal_fst (pullback.snd f.left v.left)) sq' N hN hA hX'
    let := (Etale.FiniteRingSectionDeformation.bundleAdjoint_isIso N hN A hA
      (pullback f.left v.left) hX' d
      (ConormalGradedAlgebra.piece (pullback.diagonal (pullback.snd f.left v.left)) 1)).2
    apply (cancel_mono (Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
      N hN A hA (pullback f.left v.left) hX' d
      (ConormalGradedAlgebra.piece (pullback.diagonal (pullback.snd f.left v.left)) 1) ≫
      normalSectionMap A d
        (pullback.fst (pullback.snd f.left v.left) (pullback.snd f.left v.left))
        (pullback.diagonal (pullback.snd f.left v.left))
        (pullback.diagonal_fst (pullback.snd f.left v.left)) sq')).mp
    rw [Category.assoc, integratedSpecialization_normalization]
    exact heq'.symm
  have hψ := integratedSpecialization_baseChange A N hN hA d
    (pullback.fst f.left f.left)
    (pullback.fst (pullback.snd f.left v.left) (pullback.snd f.left v.left))
    (pullback.diagonal f.left) (pullback.diagonal (pullback.snd f.left v.left))
    (pullback.diagonal_fst f.left)
    (pullback.diagonal_fst (pullback.snd f.left v.left))
    (pullback.fst f.left v.left) (diagonalCubeMap f.left v.left)
    (cube_projection_squares f.left v.left).1 (cube_diagonal f.left v.left)
    sq sq' hX hX' κ κ' hκ hκ'
  have hdiag := diagonal_factor_baseChange A f.left v.left d
  have hforward : dualizingComplexBaseChangeMap A
        (IsPullback.of_hasPullback f.left v.left) ≫ alpha'.hom =
      (ordinaryFinitePullback A (pullback.fst f.left v.left)).map alpha.hom ≫
        (vectorIntegrationBaseCoefficientPullback A N hA
          (PurityFiniteSetting.purityTwistTransport A N hN hA)
          (pullback.fst f.left v.left) hX d).hom := by
    rw [halpha, halpha', Functor.map_comp, ← Category.assoc, ← hdiag, Category.assoc]
    simpa only [Category.assoc, ψ, ψ', ordinaryFinitePullback, N] using congrArg (fun z ↦
      (ordinaryFinitePullback A (pullback.fst f.left v.left)).map
        (finiteSmoothDiagonalFactor A f.left) ≫ z) hψ.symm
  apply (cancel_mono alpha'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hforward, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The finite tensor/counit factor, before applying site comparison.
Reuse the dualizing-tensor calculation and commute its maps through symmetry. -/
private theorem tensor_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback a f' f v) (K : Etale.DerivedCategoryModule A Y) :
    (Etale.ordinaryFinitePullback A a).map
        (Etale.smoothTensorDualityMap A f
          (Etale.isIso_projectionMap_of_finite A f) K) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app K =
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a
        ((Etale.ordinaryFinitePullback A f).obj K)
        (Etale.dualizingComplex A f)).hom ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X').map
        (Etale.derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A) sq.toCommSq K)).app _ ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X').obj
        ((Etale.ordinaryFinitePullback A f').obj
          ((Etale.ordinaryFinitePullback A v).obj K))).map
        (Etale.dualizingComplexBaseChangeMap A sq) ≫
      Etale.smoothTensorDualityMap A f'
        (Etale.isIso_projectionMap_of_finite A f')
        ((Etale.ordinaryFinitePullback A v).obj K) := by
  let := Etale.derivedBraidedCategory A X
  let := Etale.derivedBraidedCategory A X'
  rw [Etale.smoothTensorDualityMap_eq, Etale.smoothTensorDualityMap_eq]
  have ht := Etale.CanonicalSmoothBaseChange.dualizing_tensor_base_change A sq K
  dsimp only [Etale.dualizingComplexTensorMap] at ht
  dsimp only [Etale.ordinaryFinitePullback, Etale.dualizingComplexTensorMap]
  rw [Functor.map_comp, Category.assoc, ht]
  have hb := Etale.leftDerivedUpperStar_map_braiding_hom_δ
    (ModuleCat.{u + 1} A) a ((Etale.ordinaryFinitePullback A f).obj K)
    (Etale.dualizingComplex A f)
  simp only [Etale.leftDerivedUpperStar_δ_eq,
    ← Etale.leftDerivedUpperStarTensorIso_hom] at hb
  dsimp only [Etale.ordinaryFinitePullback] at hb
  rw [reassoc_of% hb]
  simp only [Etale.derivedTensor_map_app, Etale.derivedTensor_obj_map]
  rw [← BraidedCategory.braiding_naturality_right_assoc,
    ← BraidedCategory.braiding_naturality_left_assoc]
  rw [whisker_exchange_assoc]

/-- Compose the ordinary orientation and tensor factors to obtain gamma.
Only monoidal pullback naturality and functoriality of tensor are used here. -/
private theorem gamma_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback a f' f v) (K : Etale.DerivedCategoryModule A Y)
    (L : Etale.DerivedCategoryModule A X) (L' : Etale.DerivedCategoryModule A X')
    (alpha : Etale.dualizingComplex A f ≅ L)
    (alpha' : Etale.dualizingComplex A f' ≅ L')
    (t : (Etale.ordinaryFinitePullback A a).obj L ≅ L')
    (ho : (Etale.ordinaryFinitePullback A a).map alpha.inv ≫
      Etale.dualizingComplexBaseChangeMap A sq = t.hom ≫ alpha'.inv)
    (ht : (Etale.ordinaryFinitePullback A a).map
        (Etale.smoothTensorDualityMap A f
          (Etale.isIso_projectionMap_of_finite A f) K) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app K =
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a
        ((Etale.ordinaryFinitePullback A f).obj K)
        (Etale.dualizingComplex A f)).hom ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X').map
        (Etale.derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A) sq.toCommSq K)).app _ ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X').obj
        ((Etale.ordinaryFinitePullback A f').obj
          ((Etale.ordinaryFinitePullback A v).obj K))).map
        (Etale.dualizingComplexBaseChangeMap A sq) ≫
      Etale.smoothTensorDualityMap A f'
        (Etale.isIso_projectionMap_of_finite A f')
        ((Etale.ordinaryFinitePullback A v).obj K)) :
    (Etale.ordinaryFinitePullback A a).map
        (Etale.FiniteSmoothPurity.gamma A f L alpha K) ≫
      (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app K =
    (Etale.ordinaryFiniteTwistedPullbackComparison A f f' v a L L' K
      ((Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app K)
      t).hom ≫ Etale.FiniteSmoothPurity.gamma A f' L' alpha'
        ((Etale.ordinaryFinitePullback A v).obj K) := by
  dsimp only [Etale.FiniteSmoothPurity.gamma, Etale.FiniteSmoothPurity.puritySource,
    Functor.comp_obj, Functor.flip_obj_obj]
  dsimp only [Etale.ordinaryFinitePullback] at *
  rw [Functor.map_comp, Category.assoc, ht]
  rw [Etale.leftDerivedUpperStarTensorIso_hom_naturality_right_assoc]
  have hn := ((Etale.derivedTensor (ModuleCat.{u + 1} A) X').map
    (Etale.derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A) sq.toCommSq K)).naturality
      ((Etale.ordinaryFinitePullback A a).map alpha.inv)
  dsimp only [Etale.ordinaryFinitePullback] at hn
  rw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc, ho, Functor.map_comp]
  simp only [Etale.ordinaryFiniteTwistedPullbackComparison,
    Etale.ordinaryFiniteTensorPullback, Etale.ordinaryFiniteTensorRightMapIso,
    Etale.derivedTensorRightCompLeftDerivedUpperStarIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  rfl

/-- Finite-ring orientation, tensor-mate, and purity-map base-change equations.
The two orientations are the ones with the dependency's actual diagonal/Rees/integration
normalization. Applying comparison gives precisely the pro-etale equations on all
constructible finite-Tor etale-origin representatives. Every intrinsic ctf object
has such an origin, and the equations use the canonical site comparisons.
Source: latest blueprint base-change factors, (1), (2), and the consequence
(blueprint: det-sp-purity-bc-factors).

Proof:
1. At Z/ell^n use the diagonal exchange cube, normalized Rees specialization and
vector-bundle integration to compare the direct diagonal orientations. The defining
OrientationNormalized equation identifies these with alpha and alpha'. Invert to
obtain the orientation identity. Transport to arbitrary finite A using the canonical
coefficient-exchange square and the general-ring orientation normalization.
2. Transpose the two tensor maps through the primed compact-support adjunction.
The mate identity expresses the transpose of the pulled-back tensor map as inverse
compact-support base change followed by the pulled-back projection/counit composite.
Compact-projection base change, naturality and the unit-component mate identity identify
it with the transpose of the primed tensor map. Injectivity of the Hom bijection gives
(2). This is the ordinary etale-origin presentation of the intrinsic pro-etale square.
3. Expand gamma. Naturality of monoidal pullback and of the tensor square comparison
moves the pulled-back orientation next to the unit exchange. Substitute step 1 and use
functoriality of tensor. Apply the comparison functor to all three ordinary equations. -/
theorem finite_factors_field
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ ringChar k)
    (X Y Y' : Over (Spec (.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (d : ℕ)
    [IsSeparated f.left] [QuasiCompact f.left] [HasCompactification f.left]
    [SmoothOfRelativeDimension d f.left]
    [IsNoetherian (pullback f.left v.left)]
    (n : ℕ) (hn : 1 ≤ n) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ell ^ n : ℕ) : A) = 0)
    (g : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f.left f.left) (pullback.diagonal f.left))
    (g' : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst (pullback.snd f.left v.left) (pullback.snd f.left v.left))
      (pullback.diagonal (pullback.snd f.left v.left)))
    (hX : IsUnit ((ell ^ n : ℕ) : Γ(X.left, ⊤)))
    (hX' : IsUnit ((ell ^ n : ℕ) : Γ(pullback f.left v.left, ⊤)))
    (alpha : Etale.dualizingComplex A f.left ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA X.left d)
    (alpha' : Etale.dualizingComplex A
        (pullback.snd f.left v.left) ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA (pullback f.left v.left) d)
    (_ha : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA f.left d g hX alpha)
    (_ha' : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA (pullback.snd f.left v.left)
      d g' hX' alpha') :
    (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
        ((Etale.ordinaryFinitePullback A (pullback.fst f.left v.left)).map alpha.inv ≫
          Etale.dualizingComplexBaseChangeMap A
            (IsPullback.of_hasPullback f.left v.left)) =
      (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
        ((Etale.vectorIntegrationBaseCoefficientPullback A (ell ^ n) hA
          (PurityFiniteSetting.purityTwistTransport A (ell ^ n)
            (pow_pos (Fact.out : ell.Prime).pos n) hA)
          (pullback.fst f.left v.left) hX d).hom ≫ alpha'.inv) ∧
    ∀ K : Etale.DerivedCategoryModule A Y.left,
      Etale.FiniteSmoothPurity.IsCtf A Y.left
        ((Etale.FiniteSmoothPurity.comparison A Y.left).obj K) →
      (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
          ((Etale.ordinaryFinitePullback A (pullback.fst f.left v.left)).map
              (Etale.smoothTensorDualityMap A f.left
                (Etale.isIso_projectionMap_of_finite A f.left) K) ≫
            (Etale.rightDerivedUpperShriekBaseChangeMap A
              (IsPullback.of_hasPullback f.left v.left)).app K) =
        (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
          ((Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
              (pullback.fst f.left v.left)
              ((Etale.ordinaryFinitePullback A f.left).obj K)
              (Etale.dualizingComplex A f.left)).hom ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) (pullback f.left v.left)).map
              (Etale.derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
                (IsPullback.of_hasPullback f.left v.left).toCommSq K)).app _ ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) (pullback f.left v.left)).obj
              ((Etale.ordinaryFinitePullback A (pullback.snd f.left v.left)).obj
                ((Etale.ordinaryFinitePullback A v.left).obj K))).map
                  (Etale.dualizingComplexBaseChangeMap A
            (IsPullback.of_hasPullback f.left v.left)) ≫
            Etale.smoothTensorDualityMap A
              (pullback.snd f.left v.left)
              (Etale.isIso_projectionMap_of_finite A (pullback.snd f.left v.left))
              ((Etale.ordinaryFinitePullback A v.left).obj K)) ∧
      (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
          ((Etale.ordinaryFinitePullback A (pullback.fst f.left v.left)).map
              (Etale.FiniteSmoothPurity.gamma A f.left _ alpha K) ≫
            (Etale.rightDerivedUpperShriekBaseChangeMap A
              (IsPullback.of_hasPullback f.left v.left)).app K) =
        (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
          ((Etale.ordinaryFiniteTwistedPullbackComparison A f.left
              (pullback.snd f.left v.left) v.left (pullback.fst f.left v.left)
              (Etale.FiniteSmoothPurity.line A (ell ^ n) hA X.left d)
              (Etale.FiniteSmoothPurity.line A (ell ^ n) hA (pullback f.left v.left) d) K
              ((Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
                (IsPullback.of_hasPullback f.left v.left).toCommSq).symm.app K)
              (Etale.vectorIntegrationBaseCoefficientPullback A (ell ^ n) hA
                (PurityFiniteSetting.purityTwistTransport A (ell ^ n)
                  (pow_pos (Fact.out : ell.Prime).pos n) hA)
                (pullback.fst f.left v.left) hX d)).hom ≫
            Etale.FiniteSmoothPurity.gamma A (pullback.snd f.left v.left) _ alpha'
              ((Etale.ordinaryFinitePullback A v.left).obj K)) := by
  have ho := finite_orientation_base_change_field k ell X Y Y' f v d n hn A hA
    g g' hX hX' alpha alpha' _ha _ha'
  refine ⟨congrArg (fun z ↦
    (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map z) ho, ?_⟩
  intro K _hK
  have ht := tensor_base_change A (IsPullback.of_hasPullback f.left v.left) K
  refine ⟨congrArg (fun z ↦
    (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map z) ht, ?_⟩
  apply congrArg (fun z ↦
    (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map z)
  exact gamma_base_change A (IsPullback.of_hasPullback f.left v.left) K
    _ _ alpha alpha' _ ho ht

/-- Extend an orientation witness by an additional factor calculation.
The generic eliminator keeps the large tower predicates out of case-split motives. -/
private theorem extend_factor_pair
    {S T : Type*} {HS : S → Prop} {HT : T → Prop}
    {HO HF : S → T → Prop}
    (h : ∃ s t, HS s ∧ HT t ∧ HO s t)
    (k : ∀ s t, HS s → HT t → HO s t → HF s t) :
    ∃ s t, HS s ∧ HT t ∧ HO s t ∧ HF s t := by
  obtain ⟨s, t, hs, ht, ho⟩ := h
  exact ⟨s, t, hs, ht, ho, k s t hs ht ho⟩

/-- Compose orientation and tensor-factor squares using only bifunctoriality.
Keeping this argument generic avoids repeated reduction of the tower realizations. -/
private theorem tensor_factors_compose
    {C C' : Type*} [Category C] [Category C']
    (U : C ⥤ C') (T : C × C ⥤ C) (T' : C' × C' ⥤ C')
    {A L W N : C} {A' L' W' N' : C'}
    {a : L ⟶ W} {a' : L' ⟶ W'}
    {e : U.obj W ⟶ W'} {t : U.obj L ⟶ L'}
    {g : T.obj (A, W) ⟶ N} {g' : T'.obj (A', W') ⟶ N'}
    {b : U.obj N ⟶ N'}
    {cL : U.obj (T.obj (A, L)) ⟶ T'.obj (A', U.obj L)}
    {cW : U.obj (T.obj (A, W)) ⟶ T'.obj (A', U.obj W)}
    (hn : U.map (T.map (Prod.mkHom (𝟙 A) a)) ≫ cW =
      cL ≫ T'.map (Prod.mkHom (𝟙 A') (U.map a)))
    (ho : U.map a ≫ e = t ≫ a')
    (ht : U.map g ≫ b = cW ≫ T'.map (Prod.mkHom (𝟙 A') e) ≫ g') :
    U.map (T.map (Prod.mkHom (𝟙 A) a) ≫ g) ≫ b =
      cL ≫ T'.map (Prod.mkHom (𝟙 A') t) ≫
        (T'.map (Prod.mkHom (𝟙 A') a') ≫ g') := by
  rw [U.map_comp, Category.assoc, ht]
  rw [← Category.assoc _ cW, hn]
  simp only [Category.assoc, ← Functor.map_comp_assoc, prod_comp,
    Category.id_comp, ho]

section TowerStatement
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
  (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
  (q : SpTowerCalculus.Coordinates ell E b)

end TowerStatement
end AlgebraicGeometry.ProEtale.SmoothPurityBaseChange
