/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit

/-!
# Composites of left derived functors of exact functors, through an isomorphism

For exact functors `F : C ⥤ D`, `G : D ⥤ E`, `H : C ⥤ E` and an isomorphism `e : F ⋙ G ≅ H`, the
isomorphism `LF ⋙ LG ≅ L(F ⋙ G) ≅ LH` is, on the image of an object of the homotopy category and
modulo the counits, induced by `e` on the homotopy categories
(`CategoryTheory.Functor.leftDerivedFunctorCompIso_symm_trans_natIso_hom_app_Qh`).
-/

@[expose] public section

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open MonoidalCategory

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

/-- The isomorphism `LF ⋙ LG ≅ L(F ⋙ G) ≅ LH` induced by `e : F ⋙ G ≅ H` is, modulo the counits,
`e` on the homotopy categories. -/
@[reassoc]
lemma leftDerivedFunctorCompIso_symm_trans_natIso_hom_app_Qh (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] {H : C ⥤ E} [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ⋙ G ≅ H)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    ((F.leftDerivedFunctorCompIso G).symm ≪≫ (F ⋙ G).leftDerivedFunctorNatIso e).hom.app
        (DerivedCategory.Qh.obj K) ≫ H.leftDerivedFunctorCounit.app K =
      G.leftDerivedFunctor.map (F.leftDerivedFunctorCounit.app K) ≫
        G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app K) := by
  rw [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    leftDerivedFunctorNatIso_hom_app_Qh, ← leftDerivedFunctorCompIso_hom_app_Qh_assoc,
    Iso.inv_hom_id_app_assoc]
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rfl

end CategoryTheory.Functor
