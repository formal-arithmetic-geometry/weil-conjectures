/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-!
# Counits of the left derived functors of exact functors and composition

For an exact functor `F`, the counit of the left derived functor `L(F)` is read off from the
isomorphism `L(F) ≅ D(F)` (`CategoryTheory.Functor.leftDerivedFunctorCounit_app_eq`). For exact
functors `F`, `G`, `H` and an isomorphism `e : H ≅ F ⋙ G`, the composition isomorphism
`L(H) ≅ L(F) ⋙ L(G)` is compatible with the counits
(`CategoryTheory.Functor.leftDerivedFunctorCompIso_hom_app_comp_counit`).
-/

@[expose] public section

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open MonoidalCategory

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
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

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

omit [HasDerivedCategory D] [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D] [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D] in
/-- For an exact functor `F`, the counit of the left derived functor `L(F)` at `K` is the
isomorphism `L(F) ≅ D(F)` followed by the factorization `D(F) ∘ Qh ≅ Qh ∘ K(F)`. -/
lemma leftDerivedFunctorCounit_app_eq [HasDerivedCategory.{wD} D]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    F.leftDerivedFunctorCounit.app K = F.leftDerivedFunctorIsoMapDerivedCategory.hom.app
      (DerivedCategory.Qh.obj K) ≫ F.mapDerivedCategoryFactorsh.hom.app K := by
  rw [← leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  rfl

/-- **The counit of `L(G) ∘ L(F)`.** For exact functors `F`, `G`, `H` and an isomorphism
`e : H ≅ F ⋙ G`, the composition isomorphism `L(H) ≅ L(F) ⋙ L(G)` obtained from
`Functor.leftDerivedFunctorNatIso` and `Functor.leftDerivedFunctorCompIso` is compatible with the
counits of the left derived functors:
```
  L(H)(Qh K) ──────≅──────▶ L(G)(L(F)(Qh K)) ──L(G)(counit)──▶ L(G)(Qh(F K))
       │                                                            │
       │ counit                                                     │ counit
       ▼                                                            ▼
   Qh(H K) ─────────────────────Qh(e)────────────────────────▶ Qh(G(F K))
```
-/
@[reassoc]
lemma leftDerivedFunctorCompIso_hom_app_comp_counit (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] {H : C ⥤ E} [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : H ≅ F ⋙ G)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (leftDerivedFunctorNatIso H e ≪≫ leftDerivedFunctorCompIso F G).hom.app
        (DerivedCategory.Qh.obj K) ≫
      G.leftDerivedFunctor.map (F.leftDerivedFunctorCounit.app K) ≫
        G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory _).obj K) =
      H.leftDerivedFunctorCounit.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom _).app K) := by
  rw [leftDerivedFunctorCounit_app_eq G, leftDerivedFunctorCounit_app_eq H]
  simp only [leftDerivedFunctorNatIso, leftDerivedFunctorCompIso, Iso.trans_hom,
    NatTrans.comp_app, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app,
    whiskerLeft_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← G.leftDerivedFunctorIsoMapDerivedCategory.inv.naturality_assoc]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, leftDerivedFunctorCounit_app_eq F,
    Iso.inv_hom_id_app_assoc, ← mapDerivedCategoryNatIso_fach]
  congr 2
  rw [← mapDerivedCategoryCompIso_fach, mapHomotopyCategoryCompIso_refl_hom_app]
  erw [Functor.map_id, Category.comp_id]

end CategoryTheory.Functor
