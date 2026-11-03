/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorTensorSiteEquations
import all WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleOrigin
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTensoratorSignedSymmetry
import all WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import all WeilConjectures.AlgebraicGeometry.Sp.SpDirectImageEtaleMate
import all WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence

/-! # Signed-symmetry pasting for the canonical compact-support comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

attribute [local implicit_reducible] Scheme.Modules
  Etale.vectorBundlePurityLower Etale.vectorBundlePurityCompactification
  Etale.vectorIntegrationSource
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem symmetry_component
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (M N : DerivedCategory C) :
    (((DerivedCategory.canonicalTensorSymmetry C).hom.app M).app N) =
      (derivedTensorKoszulSymmetry C M N).hom := by
  rw [DerivedCategory.canonicalTensorSymmetry_eq]
  rfl

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem module_braiding_eq (A : Type (u + 1)) [CommRing A] :
    (SymmetricCategory.toBraidedCategory (C := ModuleCat.{u + 1} A)) =
      (@ModuleCat.MonoidalCategory.instBraidedCategory A _) := by
  rfl

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem symmetry_koszul_transport
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (b : BraidedCategory B) (hb : b = SymmetricCategory.toBraidedCategory)
    (T : Scheme.{u})
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) B)) :
    HEq (((symmetry B T).hom.app M).app N)
      (letI : BraidedCategory B := b
       (derivedTensorKoszulSymmetry (Sheaf (Scheme.ProEt.topology T) B) M N).hom) := by
  subst b
  simpa only [symmetry] using
    heq_of_eq (symmetry_component (Sheaf (Scheme.ProEt.topology T) B) M N)

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem comparison_symmetry
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (M N : Etale.DerivedCategoryModule A T) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
        (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app M).app N) ≫
      (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A) N).hom.app M =
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) M).hom.app N ≫
      (((symmetry (ModuleCat.{u + 1} A) T).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M)).app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj N)) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have h := comparisonTensorator_signedSymmetry A T M N
  have hb := symmetry_koszul_transport (ModuleCat.{u + 1} A)
    (@ModuleCat.MonoidalCategory.instBraidedCategory A _) (module_braiding_eq A).symm T
    ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M)
    ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj N)
  rw [← eq_of_heq hb] at h
  simpa only [comparison, geoP1Comparison, Iso.app_hom] using h

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem pullback_comparison_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullback A f = comparisonOpenDerivedPullbackIso A f := by
  unfold pullback
  rw [pullComparison_eq, sp_pullback_square, comparisonPullback_transport]
  rfl

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem compact_comparison_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    {M N : Etale.DerivedCategoryModule A X}
    (hM : DerivedCategory.TStructure.t.plus M) (hN : DerivedCategory.TStructure.t.plus N)
    (b : M ⟶ N) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map b) ≫
      (compactSupportSiteComparison A c).inv.app ⟨N, hN⟩ =
    (compactSupportSiteComparison A c).inv.app ⟨M, hM⟩ ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map b) := by
  exact (compactSupportSiteComparison A c).inv.naturality
    (ObjectProperty.homMk b : ⟨M, hM⟩ ⟶ ⟨N, hN⟩)

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
