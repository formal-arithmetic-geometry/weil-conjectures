/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Derived squares of exact functors on localized complexes

On the image of a complex, the derived square isomorphism
`CategoryTheory.Functor.mapDerivedCategorySquareIso` of a square of exact functors is the
localization of the ordinary square, up to the factorization isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  (F₁ : A ⥤ B) (F₂ : B ⥤ D) (F₃ : A ⥤ C) (F₄ : C ⥤ D)
  [F₁.Additive] [F₂.Additive] [F₃.Additive] [F₄.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits F₃] [PreservesFiniteColimits F₃]
  [PreservesFiniteLimits F₄] [PreservesFiniteColimits F₄]

/-- The derived square of exact functors on the image of a complex is the localization of
the ordinary square, up to the factorization isomorphisms. -/
theorem mapDerivedCategorySquareIso_hom_app_factors (σ : F₁ ⋙ F₂ ≅ F₃ ⋙ F₄)
    (P : CochainComplex A ℤ) :
    (mapDerivedCategorySquareIso σ).hom.app (DerivedCategory.Q.obj P) ≫
        F₄.mapDerivedCategory.map (F₃.mapDerivedCategoryFactors.hom.app P) ≫
        F₄.mapDerivedCategoryFactors.hom.app ((F₃.mapHomologicalComplex (.up ℤ)).obj P) =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P) := by
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryCompIso_hom_app_factors, mapDerivedCategoryNatIso_fac,
    ← mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ P]
  simp

end CategoryTheory.Functor
