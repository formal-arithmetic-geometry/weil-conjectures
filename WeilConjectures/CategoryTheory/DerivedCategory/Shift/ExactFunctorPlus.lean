/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-!
# Isomorphisms between functors induced on bounded below derived categories commute with shifts

For exact functors between abelian categories, the isomorphisms
`Functor.mapDerivedCategoryPlusNatIso e : D⁺(F) ≅ D⁺(G)` and
`Functor.mapDerivedCategoryPlusCompIso F G : D⁺(F ⋙ G) ≅ D⁺(F) ⋙ D⁺(G)` commute with the shifts.
These are the bounded below versions of
`CategoryTheory.Functor.commShift_mapDerivedCategoryNatIso_hom` and
`CategoryTheory.Functor.commShift_mapDerivedCategoryCompIso_hom`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

instance commShift_mapDerivedCategoryPlusNatIso_hom {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    NatTrans.CommShift (mapDerivedCategoryPlusNatIso e).hom ℤ := by
  have eq : whiskerLeft DerivedCategory.Plus.Qh (mapDerivedCategoryPlusNatIso e).hom =
      F.mapDerivedCategoryPlusFactorsh.hom ≫
        whiskerRight (NatTrans.mapHomotopyCategoryPlus e.hom)
          DerivedCategory.Plus.Qh ≫ G.mapDerivedCategoryPlusFactorsh.inv := by
    refine NatTrans.ext (funext fun K => ?_)
    dsimp
    rw [← mapDerivedCategoryPlusNatIso_hom_app_factorsh_assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have : NatTrans.CommShift (whiskerLeft DerivedCategory.Plus.Qh
      (mapDerivedCategoryPlusNatIso e).hom) ℤ := by
    rw [eq]; infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Plus.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Plus.Qh.objObjPreimageIso X).inv, inferInstance⟩)

instance commShift_mapDerivedCategoryPlusCompIso_hom (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    NatTrans.CommShift (mapDerivedCategoryPlusCompIso F G).hom ℤ := by
  have eq : whiskerLeft DerivedCategory.Plus.Qh (mapDerivedCategoryPlusCompIso F G).hom =
      (F ⋙ G).mapDerivedCategoryPlusFactorsh.hom ≫
        whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv
          DerivedCategory.Plus.Qh ≫
        (Functor.associator _ _ _).hom ≫
        whiskerLeft F.mapHomotopyCategoryPlus G.mapDerivedCategoryPlusFactorsh.inv ≫
        (Functor.associator _ _ _).inv ≫
        whiskerRight F.mapDerivedCategoryPlusFactorsh.inv G.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom := by
    refine NatTrans.ext (funext fun K => ?_)
    simp [← mapDerivedCategoryPlusCompIso_fac (F := F) (G := G) K]
  have : NatTrans.CommShift (whiskerLeft DerivedCategory.Plus.Qh
      (mapDerivedCategoryPlusCompIso F G).hom) ℤ := by
    rw [eq]; infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Plus.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Plus.Qh.objObjPreimageIso X).inv, inferInstance⟩)

end CategoryTheory.Functor
