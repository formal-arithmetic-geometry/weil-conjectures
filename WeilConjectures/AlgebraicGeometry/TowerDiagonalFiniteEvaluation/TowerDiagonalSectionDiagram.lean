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
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation

/-! # The normalized diagonal and deformation diagram on towers

Source: latest blueprint, tower-geometric gamma proof (1), diagonal and deformation
(blueprint: lem-pur-tower-diagonal-section-diagram).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.TowerDiagonalFiniteEvaluation

/-- The seven diagonal, section, and fibre equations, before specialization and bundle
integration. Source: tower-geometric gamma proof (1)
(blueprint: lem-pur-tower-diagonal-section-diagram). -/
structure SectionLaws (D : Data.{u}) (U : Evaluations D)
    (finiteκ : ∀ n : ℕ, Kappa D n)
    (β : omega D.ell (scalars D) D.b D.o D.coords D.towerF ≅ C D)
    (κ : family D ≅ (inverseImage D (a D)).obj (C D))
    (s₀ : C D ≅ (inverseImage D (i₀ D)).obj ((inverseImage D (a D)).obj (C D)))
    (s₁ : C D ≅ (inverseImage D (AffineSpace.oneSection (ULift.{u} (Fin 1)) D.X)).obj
      ((inverseImage D (a D)).obj (C D)))
    (η : (inverseImage D (i₀ D)).obj (family D) ≅ normal D)
    (θ : (inverseImage D (AffineSpace.oneSection (ULift.{u} (Fin 1)) D.X)).obj
      (family D) ≅ C D) : Prop where
  /-- Delta^*v_p1 (beta)_n = beta_n v_f. -/
  beta_evaluation : ∀ n : ℕ,
    (ev D D.X n).map β.hom ≫ vC D U n = vF D U n ≫ (nu D n D.X).map (beta_n D n)
  /-- Evaluation of kappa uses v_h and v_p1, and the fixed normalized finite kappa. -/
  kappa_evaluation : ∀ n : ℕ,
    (ev D (A D) n).map κ.hom ≫ vPullC D U (a D) n =
      vFamily D U n ≫ (nu D n (A D)).map (finiteκ n).hom
  /-- s0 is the canonical section compositor, characterized by its finite word. -/
  zero_section : ∀ n : ℕ,
    (ev D D.X n).map s₀.hom ≫
        pullV D.ell (scalars D) D.b D.o (i₀ D) n
          ((inverseImage D (a D)).obj (C D))
          ((Etale.ordinaryFinitePullback (An D n) (a D)).obj
            (Etale.sectionInvariant (An D n) (p₁ D) (Δ D))) (vPullC D U (a D) n) =
      vC D U n ≫ (nu D n D.X).map
        ((Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} (An D n))
          (i₀ D) (a D) (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) D.X)).inv.app _)
  /-- The same section compositor at one. -/
  one_section : ∀ n : ℕ,
    (ev D D.X n).map s₁.hom ≫
        pullV D.ell (scalars D) D.b D.o
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) D.X) n
          ((inverseImage D (a D)).obj (C D))
          ((Etale.ordinaryFinitePullback (An D n) (a D)).obj
            (Etale.sectionInvariant (An D n) (p₁ D) (Δ D))) (vPullC D U (a D) n) =
      vC D U n ≫ (nu D n D.X).map
        ((Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} (An D n))
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) D.X) (a D)
          (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) D.X)).inv.app _)
  /-- eta is fixed by the actual exceptional zero-fibre mate, including v_h. -/
  zero_fibre : ∀ n : ℕ,
    (ev D D.X n).map η.hom ≫ vNormal D U n =
      vFibre D U (i₀ D) n ≫ (nu D n D.X).map
        (Etale.NoetherianSectionSpecialization.atZero (An D n) (p₁ D) (Δ D))
  /-- theta is fixed by the actual exceptional one-fibre mate, including v_h. -/
  one_fibre : ∀ n : ℕ,
    (ev D D.X n).map θ.hom ≫ vC D U n =
      vFibre D U (AffineSpace.oneSection (ULift.{u} (Fin 1)) D.X) n ≫
        (nu D n D.X).map (Etale.NoetherianSectionSpecialization.atOne
          (An D n) (p₁ D) (Δ D) (pullback.diagonal_fst (D.j ≫ D.p)))
  /-- The tower comparison itself is normalized at t=1. -/
  normalized_at_one :
    (inverseImage D (AffineSpace.oneSection (ULift.{u} (Fin 1)) D.X)).map κ.hom ≫
      s₁.inv = θ.hom

/-- Construct the diagonal mate, both exceptional fibre mates, and the normalized
coordinate-deformation comparison as maps of actual towers, with their finite equations.
This statement contains neither bundle integration nor the specialization equation.

Source: latest blueprint, tower-geometric gamma proof (1), first and third sentences;
parent node lem-pur-tower-diagonal-finite-evaluation, Steps 2--6
(blueprint: lem-pur-tower-diagonal-section-diagram).

Proof:
1. Compare the four given representing pairs with the chart adjunctions of tower gluing
by their counits. At the unit, the ordinary etale origin of evaluation is the constant
coefficient object. Fully faithful bounded-below site comparison transports the constant
unit isomorphism back to that origin. The section-normalized constant/root comparisons
and signed K-flat tensor realization give Evaluations, with the displayed UnitCoordinates
normalization. No arbitrary finite comparison is inserted.
2. Form the compact-support exchange on systems from its proper/open adjunction word.
SemilinearDerivedSections.evaluation_mate and the retained counit comparisons identify
its finite word, inverse, and exceptional transpose. Finite compact-support base change
and joint conservativity give invertibility on the retained etale-origin inputs. Pull
the self-base-change transpose along Delta to construct beta. Apply the same construction
to both Rees fibre squares to obtain eta and theta; evaluation gives atZero and atOne,
including the h comparison. The canonical inverse-image section compositors give s0,s1.
3. On centred smooth-section charts the local representing pairs are the same ordered
Tate lines shifted by 2d. The Rees coordinates x=t*u identify the two chart models.
Compose this chart comparison with the inverse pullback of its restriction at one,
measured against theta, so its restriction is theta exactly.
4. Finite section deformation and shifted-line normalized descent identify each finite
chart comparison with the given normalized finite kappa. On overlaps their components
therefore agree. Remove the common shift; full faithfulness of the degree-zero embedding
reduces this to equality of actual tower-sheaf maps. Glue those maps and their inverses
sectionwise. Their transition compatibility is local. This constructs kappa before
evaluation and proves all seven equations. The empty affine iteration covers d=0;
empty schemes have unique component equations, and n=0 is exponent ell.
-/
theorem section_diagram (D : Data.{u})
    (finiteκ : ∀ n : ℕ, Kappa D n)
    (hfinite : ∀ n : ℕ,
      Etale.NoetherianSectionSpecialization.Normalized (An D n) (p₁ D) (Δ D)
        (pullback.diagonal_fst (D.j ≫ D.p)) (finiteκ n)) :
    ∃ U : Evaluations D,
    ∃ β : omega D.ell (scalars D) D.b D.o D.coords D.towerF ≅ C D,
    ∃ κ : family D ≅ (inverseImage D (a D)).obj (C D),
    ∃ s₀ : C D ≅ (inverseImage D (i₀ D)).obj ((inverseImage D (a D)).obj (C D)),
    ∃ s₁ : C D ≅ (inverseImage D (AffineSpace.oneSection (ULift.{u} (Fin 1)) D.X)).obj
      ((inverseImage D (a D)).obj (C D)),
    ∃ η : (inverseImage D (i₀ D)).obj (family D) ≅ normal D,
    ∃ θ : (inverseImage D (AffineSpace.oneSection (ULift.{u} (Fin 1)) D.X)).obj
      (family D) ≅ C D,
      SectionLaws D U finiteκ β κ s₀ s₁ η θ := by sorry

end AlgebraicGeometry.ProEtale.TowerDiagonalFiniteEvaluation
