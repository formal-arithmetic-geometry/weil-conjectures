/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Compatibility of exact-right derived composition comparisons

The direct comparison and the comparison through the right derived functor of the exact
functor respect the same unit. The universal property identifies their isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The exact-right composition unit is computed by the comparison for the exact functor.
This is `rightDerivedFunctorCompMapDerivedCategoryUnit_app` without the identity composition
isomorphism in front; the primed name avoids the clash. -/
theorem rightDerivedFunctorCompMapDerivedCategoryUnit_app'
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C]
    (H : C ⥤ D) (G : D ⥤ E) [H.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (J : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit H G).app J =
      G.mapDerivedCategoryFactorsh.inv.app ((H.mapHomotopyCategory (.up ℤ)).obj J) ≫
        G.mapDerivedCategory.map (H.rightDerivedFunctorUnit.app J) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
  simp only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  have hc : (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ G)) (.up ℤ)).inv.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K) = 𝟙 _ := by
    change (HomotopyCategory.quotient E (.up ℤ)).map (𝟙 _) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  erw [hc, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The canonical exact-right composition isomorphism respects its defining unit. -/
theorem rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C]
    (H : C ⥤ D) (G : D ⥤ E) [H.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (J : HomotopyCategory C (.up ℤ)) :
    (H ⋙ G).rightDerivedFunctorUnit.app J ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso H G).hom.app
          (DerivedCategory.Qh.obj J) =
      (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit H G).app J := by
  simpa only [Functor.rightDerivedFunctorCompMapDerivedCategoryIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso_hom, Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
    Functor.rightDerivedNatTrans_app (H ⋙ G).rightDerivedFunctor
      (H.rightDerivedFunctor ⋙ G.mapDerivedCategory)
      (H ⋙ G).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit H G)
      (HomotopyCategory.quasiIso C (.up ℤ)) (𝟙 _) J

end CategoryTheory.Functor
