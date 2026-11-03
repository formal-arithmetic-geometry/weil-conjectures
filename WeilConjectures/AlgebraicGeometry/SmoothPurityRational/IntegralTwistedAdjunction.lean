/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.SpCondensedIntegralAdjunction.IntegralAdjunctionBijectionStatement
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerSectionCoordinates
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
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
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.SmoothPurity.TowerOperationsGroundFieldRetagging
import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualTowerCore
import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
import WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.TwistModelComparison
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison

/-! # Integral smooth adjunction in the signed Tate coordinates

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-rational,
sk-prop-sp-rational.proof.md, second paragraph, integral Hom bijection.
(blueprint: lem-sp-rational-integral-twisted-adjunction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.SmoothPurityRational

variable (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)

/-- The integral pullback, signed Tate tensor and even shift appearing in the middle
Hom group of the rational proof. Source: the displayed Hom calculation
(blueprint: lem-sp-rational-integral-twisted-adjunction). -/
def integralAmbientRight {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    (f : X ⟶ Y) (d : ℕ) :=
  (CondensedRing.upperStar (Profinite.padicIntegersRingObj l E.1) f.left).mapDerivedCategory ⋙
    tensorRight ((DerivedCategory.singleFunctor _ 0).obj
      (spInternalSignedTwist X.left _ (spIntegralTwist X.left l E) (d : ℤ))) ⋙
      shiftFunctor _ (2 * (d : ℤ))

/-- Restrict the given integral compactification composite, retaining all its maps.
Source: integral Hom calculation (blueprint: lem-sp-rational-integral-twisted-adjunction). -/
def integralSupport {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    {f : X ⟶ Y} (c : Compactification f.left)
    (h : ∀ M : (boundedConstructible
        (condensedRingObj (Profinite.padicIntegersRingObj l E.1) X.left)).FullSubcategory,
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj l E.1) Y.left)
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.padicIntegersRingObj l E.1) c).obj M.obj)) :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj l E.1) X.left)).FullSubcategory ⥤
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj l E.1) Y.left)).FullSubcategory :=
  ObjectProperty.lift _
    ((boundedConstructible (condensedRingObj
      (Profinite.padicIntegersRingObj l E.1) X.left)).ι ⋙
      CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.padicIntegersRingObj l E.1) c) h

/-- Restrict the specified integral twisted inverse image, retaining all its maps.
Source: integral Hom calculation (blueprint: lem-sp-rational-integral-twisted-adjunction). -/
def integralRight {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    (f : X ⟶ Y) (d : ℕ)
    (h : ∀ K : (boundedConstructible
        (condensedRingObj (Profinite.padicIntegersRingObj l E.1) Y.left)).FullSubcategory,
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj l E.1) X.left)
        ((integralAmbientRight l E f d).obj K.obj)) :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj l E.1) Y.left)).FullSubcategory ⥤
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj l E.1) X.left)).FullSubcategory :=
  ObjectProperty.lift _
    ((boundedConstructible (condensedRingObj
      (Profinite.padicIntegersRingObj l E.1) Y.left)).ι ⋙ integralAmbientRight l E f d) h

set_option maxHeartbeats 2000000 in
-- Coefficient presentation and Dbc transports share large derived functor types.
end AlgebraicGeometry.ProEtale.SmoothPurityRational
