/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-!
# Trivializations of left derived functors on objects placed in degree zero

For an exact endofunctor `I` with a trivialization `ι : I ≅ 𝟭`, the induced trivialization
`L(I) ≅ 𝟭` (`CategoryTheory.Functor.leftDerivedFunctorIdIso`) is, on an object placed in
degree zero, the trivialization `ι` placed in degree zero, read through the identification
`L(I)(X[0]) ≅ (I X)[0]`
(`CategoryTheory.Functor.leftDerivedFunctorIdIso_hom_app_singleFunctor_obj`). The same holds for
the trivialization `L(F) ⋙ L(G) ≅ L(H) ≅ 𝟭` induced by `c : H ≅ F ⋙ G` and `ι : H ≅ 𝟭`
(`CategoryTheory.Functor.leftDerivedFunctorFactorIso_symm_trans_idIso_hom_app_singleFunctor_obj`).

## Implementation details

The last two lemmas take the instances `PreservesKFlatQuasiIso` as hypotheses, rather than
deriving them from exactness, so that their statements use the same instances as concrete
derived functors which carry their own instance, such as the derived pullbacks of module objects.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]

/-- On an object placed in degree zero, the trivialization `L(I) ≅ 𝟭` induced by `ι : I ≅ 𝟭`
is `ι` placed in degree zero. -/
lemma leftDerivedFunctorIdIso_hom_app_singleFunctor_obj {I : C ⥤ C} [I.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I] (ι : I ≅ 𝟭 C) (X : C) :
    (leftDerivedFunctorIdIso ι).hom.app ((DerivedCategory.singleFunctor C 0).obj X) =
      I.singleFunctorCompLeftDerivedFunctorIso.hom.app X ≫
        (DerivedCategory.singleFunctor C 0).map (ι.hom.app X) := by
  rw [← leftDerivedFunctorNatIso_hom_app_singleFunctor_obj I (𝟭 C) ι X]
  simp only [leftDerivedFunctorIdIso, Iso.trans_hom, NatTrans.comp_app,
    singleFunctorCompLeftDerivedFunctorIso, isoWhiskerLeft_hom, whiskerLeft_app,
    mapDerivedCategoryIdIso_hom_app_singleFunctor_obj]

/-- Transport of a left derived functor along `I = I'` followed by the trivialization of `L(I')`
induced by `ι : I' ≅ 𝟭` is the trivialization of `L(I)` induced by `e ≪≫ ι`, for
`e = eqToIso h`. -/
lemma eqToIso_trans_leftDerivedFunctorIdIso {I I' : C ⥤ C}
    [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I] [I.PreservesKFlatQuasiIso]
    [I'.Additive] [PreservesFiniteLimits I'] [PreservesFiniteColimits I']
    [I'.PreservesKFlatQuasiIso] (h : I = I') (p : I.leftDerivedFunctor = I'.leftDerivedFunctor)
    (e : I ≅ I') (he : e = eqToIso h) (ι : I' ≅ 𝟭 C) :
    eqToIso p ≪≫ leftDerivedFunctorIdIso ι = leftDerivedFunctorIdIso (e ≪≫ ι) := by
  subst h he
  rw [eqToIso_refl, eqToIso_refl, Iso.refl_trans, Iso.refl_trans]

variable {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

/-- On an object placed in degree zero, the trivialization `L(F) ⋙ L(G) ≅ L(H) ≅ 𝟭` induced by
`c : H ≅ F ⋙ G` and `ι : H ≅ 𝟭` is `c⁻¹ ≫ ι` placed in degree zero, read through the
identifications `L(F)(X[0]) ≅ (F X)[0]` and `L(G)((F X)[0]) ≅ (G (F X))[0]`. -/
lemma leftDerivedFunctorFactorIso_symm_trans_idIso_hom_app_singleFunctor_obj
    {F : C ⥤ D} {G : D ⥤ C} {H : C ⥤ C}
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesKFlatQuasiIso]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.PreservesKFlatQuasiIso]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] [H.PreservesKFlatQuasiIso]
    (c : H ≅ F ⋙ G) (ι : H ≅ 𝟭 C) (X : C) :
    ((leftDerivedFunctorFactorIso c).symm ≪≫ leftDerivedFunctorIdIso ι).hom.app
        ((DerivedCategory.singleFunctor C 0).obj X) =
      G.leftDerivedFunctor.map (F.singleFunctorCompLeftDerivedFunctorIso.hom.app X) ≫
        G.singleFunctorCompLeftDerivedFunctorIso.hom.app (F.obj X) ≫
          (DerivedCategory.singleFunctor C 0).map ((c.symm ≪≫ ι).hom.app X) := by
  have h₁ := leftDerivedFunctorIdIso_hom_app_singleFunctor_obj ι X
  have h₂ : (leftDerivedFunctorFactorIso c).hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
      G.leftDerivedFunctor.map (F.singleFunctorCompLeftDerivedFunctorIso.hom.app X) ≫
        G.singleFunctorCompLeftDerivedFunctorIso.hom.app (F.obj X) =
      H.singleFunctorCompLeftDerivedFunctorIso.hom.app X ≫
        (DerivedCategory.singleFunctor C 0).map (c.hom.app X) := by
    rw [Iso.trans_hom, NatTrans.comp_app, Category.assoc,
      leftDerivedFunctorCompIso_hom_app_singleFunctor_obj F G X,
      leftDerivedFunctorNatIso_hom_app_singleFunctor_obj H (F ⋙ G) c X]
  generalize leftDerivedFunctorIdIso ι = a at h₁ ⊢
  generalize leftDerivedFunctorFactorIso c = b at h₂ ⊢
  rw [← cancel_epi (b.hom.app ((DerivedCategory.singleFunctor C 0).obj X)), reassoc_of% h₂,
    Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Iso.hom_inv_id_app_assoc, h₁, Iso.trans_hom,
    NatTrans.comp_app, Iso.symm_hom, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]

end CategoryTheory.Functor
