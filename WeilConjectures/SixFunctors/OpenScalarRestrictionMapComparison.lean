/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.OpenScalarTensorData
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTowerSupplement
public import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor
public import WeilConjectures.Algebra.Homology.ScalarInternalHomDataSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.OpenScalarTensor
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor
/-- The canonical derived restriction comparison agrees with the selected pbc comparison.
Source: Stacks 03DA; proof: apply the ordinary sectionwise uniqueness statement and then
functoriality of derived localization.
(blueprint: lem-sp-open-scalar-coefficient-restriction-map-comparison). -/
theorem pbcDerivedRestrictionMapComparison
    {T : Scheme.{u}} {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) :
    (Functor.mapDerivedCategoryNatIso
      (pbcRestrictComp (proEtaleConstantRingMap (T := T) φ)
        (proEtaleConstantRingMap (T := T) ψ)
        (proEtaleConstantRingMap (T := T) (ψ.comp φ))
        (scalarExtensionFunctor_ringMap_comp φ ψ T))).hom =
      (Functor.mapDerivedCategoryNatIso
        ((eqToIso (congrArg (fun q => pbcRestrict q)
          (scalarExtensionFunctor_ringMap_comp φ ψ T))).symm ≪≫
          CategoryTheory.scalarHomOrdinaryRestrictionComp.{u + 1, u, u + 1}
            (proEtaleConstantRingMap (T := T) φ)
            (proEtaleConstantRingMap (T := T) ψ))).inv := by
  have key : ∀ (c : proEtaleConstantRing T A ⟶ proEtaleConstantRing T C)
      (h : proEtaleConstantRingMap (T := T) φ ≫ proEtaleConstantRingMap (T := T) ψ = c),
      pbcRestrictComp (proEtaleConstantRingMap (T := T) φ)
        (proEtaleConstantRingMap (T := T) ψ) c h =
      ((eqToIso (congrArg (fun q => pbcRestrict q) h)).symm ≪≫
          CategoryTheory.scalarHomOrdinaryRestrictionComp.{u + 1, u, u + 1}
            (proEtaleConstantRingMap (T := T) φ)
            (proEtaleConstantRingMap (T := T) ψ)).symm := by
    intro c h
    subst h
    apply (pbcRestrictComp_exists _ _ _ rfl).unique
    · exact (pbcRestrictComp_exists _ _ _ rfl).exists.choose_spec
    · intro M U x
      rfl
  rw [key, Functor.mapDerivedCategoryNatIso_symm]

end AlgebraicGeometry.ProEtale.OpenScalarTensor
