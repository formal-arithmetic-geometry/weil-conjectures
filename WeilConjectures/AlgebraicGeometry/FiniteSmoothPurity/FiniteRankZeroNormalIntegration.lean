/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import all Mathlib.Logic.Small.Defs
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteEtaleSpecializationCoordinates
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.RankZeroBundleSectionCoordinates
import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingBundleSectionOrientation
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionPurityUnitNormalization
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionPurityUnitIsIso
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteUnitCoordinateIdentifications

/-! # Rank-zero normal-bundle integration in etale unit coordinates

Source: latest smooth-purity orientation proof, normal-bundle factor.
(blueprint: lem-pur-finite-rank-zero-normal-integration).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

attribute [local instance 100000] ordinaryFiniteDerivedCategoryInstance
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] CategoryTheory.catToReflQuiver Scheme.Modules
  ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
  constantComplex sectionInvariant dualizingComplex bundleSectionOmega bundleSectionObject
  affineLinearBaseCoefficient line
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
attribute [local instance 20002] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] upperStar lowerStar etaleLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  leftDerivedUpperStarIsoMapDerivedCategory

private theorem bundle_orientation_normalized
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank 0] :
    BundleSectionOrientationNormalization N hN A hA S hS 0 M
      (FiniteRingSectionDeformation.bundleOrientation N hN A hA S hS 0 M) := by
  obtain ⟨p, hp, -⟩ := bundleSectionPurityUnit_exists_isIso N hN A hA S hS 0 M
  apply bundleSectionPurityUnit_normalization N hN A hA S hS 0 M p hp
  dsimp only [FiniteRingSectionDeformation.bundleOrientation, Iso.symm_inv, asIso_hom,
    FiniteRingSectionDeformation.bundleSectionAdjoint, bundleSectionCoefficientIso]
  rw [FiniteRingSectionDeformation.bundleOrientation_purity N hN A hA S hS 0 M p hp]
  rfl

private theorem normal_section_coordinates
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S : Scheme.{u}} [IsNoetherian S]
    (g : V ⟶ S) (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [FiniteRingSectionDeformation.Geometry 0 g s]
    [Etale (Scheme.Hom.normalConeProj g s)] [IsSeparated (Scheme.Hom.normalConeProj g s)]
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C)
    (sq : IsPullback
      (reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso 0 g s).hom
      (Scheme.Hom.normalConeProj g s)
      (VectorBundleZeroSection.π S 0 (ConormalGradedAlgebra.piece s 1)) (𝟙 S))
    [Etale (VectorBundleZeroSection.π S 0 (ConormalGradedAlgebra.piece s 1))] :
    normalSectionMap A 0 g s hs sq ≫
      (finiteSmoothSectionCoordinates A C (Scheme.Hom.normalConeProj g s)
        (Scheme.Hom.normalConeZeroSection s)).hom =
      (finiteSmoothSectionCoordinates A C
        (VectorBundleZeroSection.π S 0 (ConormalGradedAlgebra.piece s 1))
        (VectorBundleZeroSection.zero S 0 (ConormalGradedAlgebra.piece s 1))).hom := by
  let M := ConormalGradedAlgebra.piece s 1
  dsimp only [normalSectionMap]
  rw [Category.assoc, section_coordinates_baseChange A sq _ _ _ C hC,
    ← derived_pullback_unit_id A S]
  have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.naturality
    (finiteSmoothSectionCoordinates A C (VectorBundleZeroSection.π S 0 M)
      (VectorBundleZeroSection.zero S 0 M)).hom
  dsimp only [M, ordinaryFinitePullback, sectionInvariant, dualizingComplex,
    FiniteRingSectionDeformation.bundleRight] at hn ⊢
  erw [← reassoc_of% hn]
  simp only [Iso.inv_hom_id_app]
  exact Category.comp_id _

private theorem comp_eq_of_inverse {C : Type*} [Category C] {X Y : C} (b : Y ⟶ X)
    (o c : X ⟶ Y) (z : Y ⟶ Y) (ho : b ≫ o = 𝟙 Y) (hc : o = c) (hz : z = 𝟙 Y) :
    b ≫ c = z := by
  rw [← hc, ho, hz]

/-- Rank-zero bundle integration and the actual cone comparison preserve the unit.
This is independent of the Rees family comparison and its normalization.
Source: sk-prop-sp-orientation.proof.md, third displayed arrow; the proof of
lem-pur-finite-smooth-gamma-normalization, Step 7; vector-bundle integration at rank zero.
(blueprint: lem-pur-finite-rank-zero-normal-integration).

Proof: a locally free module of rank zero is the zero module. Its symmetric algebra
is the structure algebra, so the bundle projection and zero section are inverse.
On each frame the zero-variable coordinate tower is the identity adjunction, whose
counit is the identity trace. The unique frame-glued vectorBundleIntegration is
therefore this trace transported by the projection. Transposing it under the fixed
compact-support adjunction identifies bundleSectionAdjoint with the inverse
coefficient-unit comparison. The specified reesConeComparison and coneBundleIso
preserve projection and zero section by their specification theorems. Their section
mate thus preserves the graph-normalized unit coordinates, by support exchange and
the two adjunction triangles. Compose and cancel the unit pullback compositors. The
remaining empty-tensor identification is zeroLineIso, giving precisely the equality
below. The calculation includes empty bases and the zero coefficient ring. -/
theorem finiteRankZeroNormalIntegration_coordinates
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S]
    (g : V ⟶ S) (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [FiniteRingSectionDeformation.Geometry 0 g s]
    [Etale (Scheme.Hom.normalConeProj g s)] [IsSeparated (Scheme.Hom.normalConeProj g s)]
    (hS : IsUnit (N : Γ(S, ⊤)))
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C)
    (sq : IsPullback
      (reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso 0 g s).hom
      (Scheme.Hom.normalConeProj g s)
      (VectorBundleZeroSection.π S 0 (ConormalGradedAlgebra.piece s 1)) (𝟙 S)) :
    FiniteRingSectionDeformation.bundleSectionAdjoint N hN A hA S hS 0
        (ConormalGradedAlgebra.piece s 1) ≫ normalSectionMap A 0 g s hs sq ≫
        (finiteSmoothSectionCoordinates A C (Scheme.Hom.normalConeProj g s)
          (Scheme.Hom.normalConeZeroSection s)).hom =
      (zeroLineIso A N hA S 0 rfl).hom := by
  let M := ConormalGradedAlgebra.piece s 1
  have := VectorTraceGeometry.zero_isIso S M
  have : Etale (VectorBundleZeroSection.π S 0 M) := inferInstance
  let o := FiniteRingSectionDeformation.bundleOrientation N hN A hA S hS 0 M
  obtain ⟨e, _, hz, he⟩ := finiteRingBundleSectionOrientation_rankZero
    N hN A hA S hS M o (bundle_orientation_normalized A N hN hA S hS M)
  rw [rankZeroBundleSection_coordinates A S M e hz C hC] at he
  have hnormal := normal_section_coordinates A g s hs C hC sq
  have := (FiniteRingSectionDeformation.bundleAdjoint_isIso N hN A hA S hS 0 M).2
  have ho : FiniteRingSectionDeformation.bundleSectionAdjoint N hN A hA S hS 0 M ≫ o.hom =
      𝟙 _ := by
    dsimp only [o, FiniteRingSectionDeformation.bundleOrientation, Iso.symm_hom, asIso_inv]
    exact IsIso.hom_inv_id _
  have hi : (zeroLineIso A N hA S 0 rfl).inv = 𝟙 _ := by
    simp only [zeroLineIso, Iso.trans_inv, eqToIso_refl, Iso.refl_inv, Category.comp_id,
      singleFunctorObjUnitIso_inv]
  have hz : (zeroLineIso A N hA S 0 rfl).hom = 𝟙 _ := by
    rw [← Category.comp_id (zeroLineIso A N hA S 0 rfl).hom, ← hi, Iso.hom_inv_id]
  exact comp_eq_of_inverse _ _ _ _ ho (he.trans hnormal.symm) hz

end AlgebraicGeometry.Etale.FiniteSmoothPurity
