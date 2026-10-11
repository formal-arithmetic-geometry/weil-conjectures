/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Counits of left derived functors of exact functors

For exact functors `F`, `G` between abelian categories with functorial flat resolutions, the
isomorphisms `Functor.leftDerivedFunctorNatIso` and `Functor.leftDerivedFunctorCompIso` are
compatible with the counits `Qh ⋙ LF ⟶ F.mapHomotopyCategory ⋙ Qh` of the left derived
functors.
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

/-- The isomorphism `Functor.leftDerivedFunctorNatIso e` induced by an isomorphism `e : F ≅ G`
of exact functors is compatible with the counits of the left derived functors. -/
@[reassoc]
lemma leftDerivedFunctorNatIso_hom_app_comp_leftDerivedFunctorCounit_app {G : C ⥤ D}
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (leftDerivedFunctorNatIso F e).hom.app (DerivedCategory.Qh.obj K) ≫
        G.leftDerivedFunctorCounit.app K =
      F.leftDerivedFunctorCounit.app K ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) := by
  rw [← F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac,
    ← G.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  simp only [leftDerivedFunctorNatIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    whiskerLeft_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [mapDerivedCategoryNatIso_fach]

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

/-- The composition isomorphism `Functor.leftDerivedFunctorCompIso F G` is compatible with the
counits of the left derived functors:
```
L(F ⋙ G)(Qh K) ──≅──▶ LG(LF(Qh K)) ──LG(counit)──▶ LG(Qh(F K)) ──counit──▶ Qh(G(F K))
        ╲                                                                    │
  counit ╲                                                                   │ =
          ▼                                                                  ▼
                              Qh((F ⋙ G) K)
``` -/
@[reassoc]
lemma leftDerivedFunctorCompIso_hom_app_comp_leftDerivedFunctorCounit_app (G : D ⥤ E)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (leftDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj K) ≫
        G.leftDerivedFunctor.map (F.leftDerivedFunctorCounit.app K) ≫
          G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
      (F ⋙ G).leftDerivedFunctorCounit.app K := by
  rw [← F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac,
    ← G.leftDerivedFunctorIsoMapDerivedCategory_hom_fac,
    ← (F ⋙ G).leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  simp only [leftDerivedFunctorCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    whiskerLeft_app, isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app,
    Category.assoc, Functor.map_comp, comp_obj]
  have h := mapDerivedCategoryCompIso_fach F G K
  rw [mapHomotopyCategoryCompIso_refl_hom_app] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  rw [← h]
  congr 1
  have hn := G.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj K) ≫
      F.mapDerivedCategoryFactorsh.hom.app K)
  simp only [comp_obj, Functor.map_comp] at hn
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Functor
