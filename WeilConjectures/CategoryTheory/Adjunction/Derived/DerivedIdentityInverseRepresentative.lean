/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso

/-! # Inverse exact-derived identity comparison on cochain representatives -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
namespace CategoryTheory.Adjunction

/-- On a cochain representative, the inverse exact-derived identity comparison is the
localized inverse chain comparison followed by the inverse localization factor.
Source: the homotopy representative formula in `AdjunctionIdIso` and Mathlib localization.
(blueprint: lem-sf-derived-identity-inverse-representative)

Proof: compose on the right with the localization factor. Apply the existing homotopy
formula to the quotient of the cochain complex. The quotient comparison and the termwise
homotopy comparison are identity maps; remove them with functoriality and cancel the factor. -/
theorem mapDerivedCategoryNatIso_trans_idIso_inv_app_Q_obj {D : Type*} [Category D] [Abelian D]
    [HasDerivedCategory D] (R : D ⥤ D) [R.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits R]
    [CategoryTheory.Limits.PreservesFiniteColimits R]
    (r : R ≅ 𝟭 D) (P : CochainComplex D ℤ) :
    (Functor.mapDerivedCategoryNatIso (C := D) (D := D) (F := R) (G := 𝟭 D) r ≪≫
      Functor.mapDerivedCategoryIdIso D).inv.app
        (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex r.inv (.up ℤ)).app P) ≫
        (Functor.mapDerivedCategoryFactors (C₁ := D) (C₂ := D) R).inv.app P := by
  have hId : (Functor.mapDerivedCategoryIdIso D).hom.app (DerivedCategory.Q.obj P) =
      (𝟭 D).mapDerivedCategoryFactors.hom.app P := by
    rw [Functor.mapDerivedCategoryIdIso_hom_app]
    have h : (Functor.mapHomologicalComplexIdIso D (.up ℤ)).hom.app P = 𝟙 _ := rfl
    rw [h]
    erw [DerivedCategory.Q.map_id, Category.comp_id]
  apply (Iso.eq_comp_inv ((Functor.mapDerivedCategoryFactors (C₁ := D) (C₂ := D) R).app P)).2
  have hh := Functor.mapDerivedCategoryNatIso_fac r.symm P
  rw [Functor.mapDerivedCategoryNatIso_symm] at hh
  simp only [Iso.trans_inv, NatTrans.comp_app, Category.assoc]
  rw [hh, ← Category.assoc, ← hId, Iso.inv_hom_id_app]
  erw [Category.id_comp]

end CategoryTheory.Adjunction
