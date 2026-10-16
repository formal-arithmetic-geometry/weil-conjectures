/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Squares induced on bounded below derived categories

A square `σ : G ⋙ L' ≅ L ⋙ G'` of exact functors between abelian categories induces a square
`G⁺ ⋙ L'⁺ ≅ L⁺ ⋙ G'⁺` of the functors induced on the bounded below derived categories
(`CategoryTheory.Functor.mapDerivedCategoryPlusSquareIso`). This file computes it on complexes
and shows that it is the restriction of the square induced on the unbounded derived categories.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory C₄]
  {L : C₂ ⥤ C₁} {L' : C₄ ⥤ C₃} {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
  [L.Additive] [L'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- The square `G⁺ ⋙ L'⁺ ≅ L⁺ ⋙ G'⁺` of functors on bounded below derived categories induced
by a square `σ : G ⋙ L' ≅ L ⋙ G'` of exact functors. -/
noncomputable abbrev mapDerivedCategoryPlusSquareIso (σ : G ⋙ L' ≅ L ⋙ G') :
    G.mapDerivedCategoryPlus ⋙ L'.mapDerivedCategoryPlus ≅
      L.mapDerivedCategoryPlus ⋙ G'.mapDerivedCategoryPlus :=
  (mapDerivedCategoryPlusCompIso G L').symm ≪≫ mapDerivedCategoryPlusNatIso σ ≪≫
    mapDerivedCategoryPlusCompIso L G'

/-- The square `G⁺ ⋙ L'⁺ ≅ L⁺ ⋙ G'⁺` induced by `σ` is computed by `σ` on complexes. -/
@[reassoc]
lemma mapDerivedCategoryPlusSquareIso_hom_app_factorsh (σ : G ⋙ L' ≅ L ⋙ G')
    (N : HomotopyCategory.Plus C₂) :
    (mapDerivedCategoryPlusSquareIso σ).hom.app (DerivedCategory.Plus.Qh.obj N) ≫
        G'.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        G'.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj N) =
      L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ.hom).app N) := by
  have h₁ := mapDerivedCategoryPlusCompIso_hom_app_factorsh L G' N
  have h₂ := mapDerivedCategoryPlusNatIso_hom_app_factorsh σ N
  have h₃ := mapDerivedCategoryPlusCompIso_hom_app_factorsh G L' N
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [h₁]
  erw [h₂]
  rw [← h₃]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The image under `DerivedCategory.Plus.ι` of the inverse of the composition isomorphism of
`mapDerivedCategoryPlus` is the inverse of the composition isomorphism of
`mapDerivedCategory`. -/
lemma ι_map_mapDerivedCategoryPlusCompIso_inv_app (X : DerivedCategory.Plus C₂) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusCompIso G L').inv.app X) =
      (mapDerivedCategoryCompIso G L').inv.app (DerivedCategory.Plus.ι.obj X) := by
  rw [← cancel_epi (DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusCompIso G L').hom.app X)),
    ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id,
    ι_map_mapDerivedCategoryPlusCompIso_hom_app, Iso.hom_inv_id_app]
  rfl

/-- The image under `DerivedCategory.Plus.ι` of the square induced by `σ` on bounded below
derived categories is the square induced by `σ` on unbounded derived categories. -/
lemma ι_map_mapDerivedCategoryPlusSquareIso_hom_app (σ : G ⋙ L' ≅ L ⋙ G')
    (X : DerivedCategory.Plus C₂) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusSquareIso σ).hom.app X) =
      (mapDerivedCategoryCompIso G L').inv.app (DerivedCategory.Plus.ι.obj X) ≫
        (mapDerivedCategoryNatIso σ).hom.app (DerivedCategory.Plus.ι.obj X) ≫
        (mapDerivedCategoryCompIso L G').hom.app (DerivedCategory.Plus.ι.obj X) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    ι_map_mapDerivedCategoryPlusCompIso_inv_app, ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    ι_map_mapDerivedCategoryPlusCompIso_hom_app]

section NatIso

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The image under `DerivedCategory.Plus.ι` of the inverse of the isomorphism induced by
`e : F ≅ G` on bounded below derived categories is the inverse of the isomorphism induced
on unbounded derived categories. -/
lemma ι_map_mapDerivedCategoryPlusNatIso_inv_app (e : F ≅ G) (X : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusNatIso e).inv.app X) =
      (mapDerivedCategoryNatIso e).inv.app (DerivedCategory.Plus.ι.obj X) := by
  rw [← cancel_epi (DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusNatIso e).hom.app X)),
    ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id,
    ι_map_mapDerivedCategoryPlusNatIso_hom_app, Iso.hom_inv_id_app]
  rfl

end NatIso

end CategoryTheory.Functor
