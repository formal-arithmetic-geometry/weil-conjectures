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

end AlgebraicGeometry.Etale.FiniteSmoothPurity
