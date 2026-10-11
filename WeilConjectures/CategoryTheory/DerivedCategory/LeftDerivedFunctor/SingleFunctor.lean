/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-!
# Left derived functors of exact functors on sheaves in degree zero

For exact functors, the isomorphisms `Functor.mapDerivedCategoryNatIso`,
`Functor.mapDerivedCategoryCompIso`, `Functor.leftDerivedFunctorNatIso` and
`Functor.leftDerivedFunctorCompIso` are, on objects placed in degree zero, the images of the
corresponding isomorphisms of the underlying functors, through the identifications
`Functor.mapDerivedCategorySingleFunctor` and `Functor.singleFunctorCompLeftDerivedFunctorIso`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- the `simp` calls unfold the single-degree identifications into a form fixed by the next steps
set_option linter.flexible false in
lemma mapDerivedCategoryNatIso_hom_app_singleFunctor_obj {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) (X : C) :
    (mapDerivedCategoryNatIso e).hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app X =
      (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (DerivedCategory.singleFunctor D 0).map (e.hom.app X) := by
  have hn := (mapDerivedCategoryNatIso e).hom.naturality
    ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app X)
  rw [← cancel_epi (F.mapDerivedCategory.map
    ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app X)),
    reassoc_of% hn]
  simp [Functor.mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ]
  erw [Functor.map_id, Functor.map_id]
  simp only [Category.id_comp]
  erw [Category.id_comp, Category.id_comp, mapDerivedCategoryNatIso_fac_assoc]
  rw [← DerivedCategory.Q.map_comp]
  change _ = _ ≫ DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map
    ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).map (e.hom.app X))
  rw [← DerivedCategory.Q.map_comp]
  congr 2
  refine HomologicalComplex.to_single_hom_ext ?_
  simp [HomologicalComplex.single_map_f_self]
  rfl


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- the `simp` calls unfold the single-degree identifications into a form fixed by the next steps
set_option linter.flexible false in
lemma mapDerivedCategoryCompIso_hom_app_singleFunctor_obj (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [PreservesFiniteLimits (F ⋙ G)]
    [PreservesFiniteColimits (F ⋙ G)] (X : C) :
    (mapDerivedCategoryCompIso F G).hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
          (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) =
      ((F ⋙ G).mapDerivedCategorySingleFunctor 0).hom.app X := by
  simp [Functor.mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ]
  erw [Functor.map_id]
  simp only [Category.id_comp]
  erw [Category.id_comp, Category.id_comp]
  have := mapDerivedCategoryCompIso_fac F G ((CochainComplex.singleFunctor C 0).obj X)
  erw [← this]
  simp only [Category.assoc]
  congr 2
  erw [← Functor.comp_map, ← Functor.comp_map, G.mapDerivedCategoryFactors.hom.naturality_assoc]
  congr 1
  simp only [Functor.comp_map, ← DerivedCategory.Q.map_comp]
  congr 1
  refine HomologicalComplex.to_single_hom_ext ?_
  simp
  erw [Category.id_comp]

end CategoryTheory.Functor

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

lemma leftDerivedFunctorNatIso_hom_app_singleFunctor_obj
    (H F : C ⥤ E) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (e : H ≅ F) (X : C) :
    (leftDerivedFunctorNatIso H e).hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        (F.singleFunctorCompLeftDerivedFunctorIso).hom.app X =
      (H.singleFunctorCompLeftDerivedFunctorIso).hom.app X ≫
        (DerivedCategory.singleFunctor E 0).map (e.hom.app X) := by
  simp [leftDerivedFunctorNatIso, singleFunctorCompLeftDerivedFunctorIso,
    mapDerivedCategoryNatIso_hom_app_singleFunctor_obj]

-- the `simp` call unfolds the compatibility isomorphisms
set_option linter.flexible false in
lemma leftDerivedFunctorCompIso_hom_app_singleFunctor_obj
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (X : C) :
    (leftDerivedFunctorCompIso F G).hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        G.leftDerivedFunctor.map ((F.singleFunctorCompLeftDerivedFunctorIso).hom.app X) ≫
          (G.singleFunctorCompLeftDerivedFunctorIso).hom.app (F.obj X) =
      ((F ⋙ G).singleFunctorCompLeftDerivedFunctorIso).hom.app X := by
  simp [leftDerivedFunctorCompIso, singleFunctorCompLeftDerivedFunctorIso]
  exact mapDerivedCategoryCompIso_hom_app_singleFunctor_obj F G X

end CategoryTheory.Functor
