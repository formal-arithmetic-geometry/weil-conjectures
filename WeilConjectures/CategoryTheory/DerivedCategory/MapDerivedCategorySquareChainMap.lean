/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# The derived square of exact functors on a complex

On the image `Q K` of a cochain complex, the isomorphism `D(F₁) ⋙ D(F₂) ≅ D(G₁) ⋙ D(G₂)`
induced by `e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂` is the localization of the levelwise square
`CategoryTheory.Functor.squareChainMap`, up to the factorization isomorphisms
(`CategoryTheory.Functor.mapDerivedCategorySquareIso_hom_app_Q`).
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E] [Abelian A]
  [Abelian B] [Abelian B'] [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory B'] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
/-- The levelwise square of complexes, with source and target in iterated form. -/
@[simps f]
def squareChainMap (e : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂) (K : CochainComplex A ℤ) :
    (F₂.mapHomologicalComplex (.up ℤ)).obj ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (G₂.mapHomologicalComplex (.up ℤ)).obj ((G₁.mapHomologicalComplex (.up ℤ)).obj K) where
  f i := e.app (K.X i)
  comm' i j _ := by simpa using (e.naturality (K.d i j)).symm

/-- On a complex, the exact descent of a square is the levelwise square, after the
factorization isomorphisms. -/
@[reassoc]
theorem mapDerivedCategorySquareIso_hom_app_Q (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (K : CochainComplex A ℤ) :
    (mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (squareChainMap e.hom K) := by
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  rw [mapDerivedCategoryCompIso_hom_app_factors, mapDerivedCategoryNatIso_fac,
    ← mapDerivedCategoryCompIso_hom_app_factors_assoc F₁ F₂ K, Iso.hom_inv_id_app_assoc]
  rfl

/-- The inverse form of `mapDerivedCategorySquareIso_hom_app_Q`. -/
@[reassoc]
theorem mapDerivedCategorySquareIso_inv_app_Q (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (K : CochainComplex A ℤ) :
    (mapDerivedCategorySquareIso e).inv.app (DerivedCategory.Q.obj K) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) =
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (squareChainMap e.inv K) := by
  have h := mapDerivedCategorySquareIso_hom_app_Q e K
  have hid : squareChainMap e.hom K ≫ squareChainMap e.inv K = 𝟙 _ := by
    ext i
    simp
  rw [← cancel_epi ((mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K)),
    Iso.hom_inv_id_app_assoc, reassoc_of% h, ← DerivedCategory.Q.map_comp, hid,
    DerivedCategory.Q.map_id, Category.comp_id]

end CategoryTheory.Functor
