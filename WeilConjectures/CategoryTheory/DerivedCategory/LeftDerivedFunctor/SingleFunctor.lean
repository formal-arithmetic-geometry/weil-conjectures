/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The functors induced on derived categories and the single-degree embeddings

For exact functors `F : C ⥤ D` and `G : D ⥤ E` and an isomorphism `e : H ≅ F ⋙ G`, the
identifications `D(H) ≅ D(F) ⋙ D(G)` (`Functor.mapDerivedCategoryNatIso`,
`Functor.mapDerivedCategoryCompIso`) are compatible with the identifications
`D(F)(X[0]) ≅ (F X)[0]` (`Functor.mapDerivedCategorySingleFunctor`): on an object placed in
degree zero they are `e` placed in degree zero
(`Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor`).
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

lemma mapDerivedCategorySingleFunctor_hom_app_eq (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (X : C) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app X =
      F.mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app X) := by
  simp [mapDerivedCategorySingleFunctor, Functor.mapCochainComplexSingleFunctor,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    DerivedCategory.singleFunctorIsoCompQ]

set_option linter.flexible false in
/-- The composite of `D(H) ≅ D(F ⋙ G) ≅ D(F) ⋙ D(G)` with the identifications of the derived
functors on objects placed in degree zero is `e` placed in degree zero. -/
lemma mapDerivedCategoryNatIso_hom_app_singleFunctor (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)]
    (e : H ≅ F ⋙ G) (X : C) :
    (mapDerivedCategoryNatIso e).hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        (mapDerivedCategoryCompIso F G).hom.app _ ≫
          G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
            (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) =
      (H.mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (DerivedCategory.singleFunctor E 0).map (e.hom.app X) := by
  rw [mapDerivedCategorySingleFunctor_hom_app_eq, mapDerivedCategorySingleFunctor_hom_app_eq,
    mapDerivedCategorySingleFunctor_hom_app_eq, Functor.map_comp]
  let K := (CochainComplex.singleFunctor C 0).obj X
  have hnat := G.mapDerivedCategoryFactors.hom.naturality
    ((F.mapCochainComplexSingleFunctor 0).hom.app X)
  have hc := mapDerivedCategoryCompIso_fac F G K
  have hc' : (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app K) := by
    rw [← hc]
    simp [← Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hnat]
  erw [reassoc_of% hc', mapDerivedCategoryNatIso_fac_assoc]
  simp only [← Functor.map_comp]
  congr 1
  rw [show (DerivedCategory.singleFunctor E 0).map (e.hom.app X) =
    DerivedCategory.Q.map ((CochainComplex.singleFunctor E 0).map (e.hom.app X)) from rfl,
    ← Functor.map_comp]
  congr 1
  ext i
  by_cases hi : i = 0
  · subst hi
    simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors, HomologicalComplex.singleMapHomologicalComplex,
      Functor.mapHomologicalComplexCompIso, HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
    erw [Category.comp_id, Category.comp_id, Category.id_comp]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt _ _

end CategoryTheory.Functor
