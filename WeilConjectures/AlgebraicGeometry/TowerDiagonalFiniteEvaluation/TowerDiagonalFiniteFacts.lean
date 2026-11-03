/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerClasses
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
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
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
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
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothTwoLevelReduction
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCompactQuotientCocycle
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothOrdinaryTwistCocycle
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarTensorComposition
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothProQuotientTransport
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothSiteRealizations
import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecialization
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange

/-! # Finite foundations for the tower diagonal diagram

The square uses the specified homogeneous Rees comparison and symmetric-algebra comparison.
Source: latest blueprint, tower-geometric gamma proof (1), geometric preparation and finite
section deformation (blueprint: lem-pur-tower-diagonal-finite-foundations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.TowerDiagonalFiniteEvaluation

private theorem normal_square (D : Data.{u}) : NormalSquare D := by
  have he : (coneBundle D).hom ≫ VectorBundleZeroSection.π D.X D.d
      (ConormalGradedAlgebra.piece (Δ D) 1) = π D := by
    dsimp [coneBundle]
    rw [Category.assoc,
      (Etale.FiniteRingSectionDeformation.coneBundleIso_spec D.d (p₁ D) (Δ D)
        (pullback.diagonal_fst (D.j ≫ D.p))).1,
      (Etale.FiniteSmoothPurity.reesConeComparison_spec (Δ D)).1]
    exact Scheme.Hom.purityNormalProjection_eq _ _ (pullback.diagonal_fst (D.j ≫ D.p))
  exact IsPullback.of_horiz_isIso ⟨by simpa using he⟩

private theorem integration_iso (D : Data.{u}) (sq : NormalSquare D) (n : ℕ) :
    IsIso (integration_n D sq n) := by
  have := (Etale.FiniteRingSectionDeformation.bundleAdjoint_isIso
    (D.ell ^ (n + 1)) (pow_pos (Fact.out : D.ell.Prime).pos _)
    (An D n) (SpTowerP1.levelAnnihilates D.ell (scalars D) n)
    D.X (units D D.Xk n) D.d (ConormalGradedAlgebra.piece (Δ D) 1)).2
  have := Etale.FiniteSmoothPurity.normalSectionMap_isIso (An D n) D.d (p₁ D) (Δ D)
    (pullback.diagonal_fst (D.j ≫ D.p)) sq
    (D.ell ^ (n + 1)) (pow_pos (Fact.out : D.ell.Prime).pos _)
    (SpTowerP1.levelAnnihilates D.ell (scalars D) n) (units D D.Xk n)
  unfold integration_n
  infer_instance

private theorem beta_iso (D : Data.{u}) (n : ℕ) : IsIso (beta_n D n) := by
  have : HasInvertibleExponent (An D n) D.X :=
    ⟨D.ell ^ (n + 1), pow_pos (Fact.out : D.ell.Prime).pos _,
      SpTowerP1.levelAnnihilates D.ell (scalars D) n, units D D.Xk n⟩
  have : IsIso (Etale.dualizingComplexBaseChangeMap (An D n)
      (IsPullback.of_hasPullback (D.j ≫ D.p) (D.j ≫ D.p)).flip) := by
    have := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension
      (An D n) (D.j ≫ D.p) D.d
      (IsPullback.of_hasPullback (D.j ≫ D.p) (D.j ≫ D.p)).flip
    exact (Etale.isIso_dualizingComplexBaseChangeMap_iff (An D n) _).2 inferInstance
  unfold beta_n Etale.finiteSmoothDiagonalFactor
  simp only [← Iso.app_inv]
  infer_instance

/-- The canonical normal-bundle square, invertibility of the specified finite integration
and diagonal factors, and existence and uniqueness of the normalized finite deformation.

Source: tower-geometric gamma proof (1), geometric preparation and finite comparisons
(blueprint: lem-pur-tower-diagonal-finite-foundations).

Proof: Compose the homogeneous Rees comparison with the symmetric normal-bundle comparison.
Their projection identities make its square with the identity of X Cartesian. The bundle
integration adjunct and the exceptional normal-section mate are invertible, so their composite
is invertible. Smooth exceptional base change and the section compositor give invertibility
of beta. Apply finite-ring normalized section deformation to (p1, Delta), with exponent
ell^(n+1), annihilator given by the coefficient quotient, and invertibility pulled from k.
The geometry instance already supplied by the smooth-section theorem gives every required
Noetherian and compactification instance. Uniqueness fixes the finite kappa, including d=0,
the first positive level n=0, and the empty scheme.
-/
theorem finite_foundations (D : Data.{u}) :
    ∃ sq : NormalSquare D,
      (∀ n : ℕ, IsIso (integration_n D sq n)) ∧
      (∀ n : ℕ, IsIso (beta_n D n)) ∧
      ∀ n : ℕ, ∃! κ : Kappa D n,
        Etale.NoetherianSectionSpecialization.Normalized (An D n) (p₁ D) (Δ D)
          (pullback.diagonal_fst (D.j ≫ D.p)) κ := by
  refine ⟨normal_square D, integration_iso D (normal_square D), beta_iso D, ?_⟩
  intro n
  exact Etale.FiniteRingSectionDeformation.existsUnique_normalized
    (D.ell ^ (n + 1)) (pow_pos (Fact.out : D.ell.Prime).pos _)
    (An D n) (SpTowerP1.levelAnnihilates D.ell (scalars D) n)
    (units D D.Xk n) D.d (p₁ D) (Δ D) (pullback.diagonal_fst (D.j ≫ D.p))

end AlgebraicGeometry.ProEtale.TowerDiagonalFiniteEvaluation
