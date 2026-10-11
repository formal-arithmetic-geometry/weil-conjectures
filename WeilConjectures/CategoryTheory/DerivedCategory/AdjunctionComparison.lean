/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-!
# Comparison of the two unbounded derived adjunctions of an exact left adjoint

Let `adj : f ⊣ g` be an adjunction of additive functors between abelian categories with `f`
exact. There are two derived adjunctions on the unbounded derived categories:

- `CategoryTheory.Adjunction.derivedAdjunction`: `f.leftDerivedFunctor ⊣ g.rightDerivedFunctor`,
  with the left adjoint derived via K-flat resolutions;
- `CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`:
  `f.mapDerivedCategory ⊣ g.rightDerivedFunctor`, with the levelwise left adjoint.

They agree: the first is the second transported along the canonical isomorphism
`f.leftDerivedFunctor ≅ f.mapDerivedCategory`
(`CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory`). This lets structures
known for the levelwise adjunction, such as the compatibility with shifts, be transported to
the derived one.

## Main results

- `CategoryTheory.Adjunction.derivedAdjunction_eq_ofNatIsoLeft`
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Abelian

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]

/-- For an exact left adjoint `f`, the derived adjunction
`f.leftDerivedFunctor ⊣ g.rightDerivedFunctor` is the adjunction
`f.mapDerivedCategory ⊣ g.rightDerivedFunctor` transported along the canonical isomorphism
`f.leftDerivedFunctor ≅ f.mapDerivedCategory`. Both units are characterised by their
compatibility with the unit of `adj` on the homotopy category. -/
theorem derivedAdjunction_eq_ofNatIsoLeft (adj : f ⊣ g) :
    adj.derivedAdjunction = adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
      f.leftDerivedFunctorIsoMapDerivedCategory.symm := by
  ext1
  apply (f.leftDerivedFunctor ⋙ g.rightDerivedFunctor).leftDerived_ext
    ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight f.leftDerivedFunctorCounit g.rightDerivedFunctor)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  ext X
  have h₁ := (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) f.leftDerivedFunctorCounit
    g.rightDerivedFunctorUnit X
  have h₂ := (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) f.mapDerivedCategoryFactorsh.hom
    g.rightDerivedFunctorUnit X
  have h₃ := NatTrans.congr_app f.leftDerivedFunctorIsoMapDerivedCategory_hom_fac X
  dsimp at h₁ h₂ h₃ ⊢
  rw [← h₃] at h₁
  simp only [Functor.map_comp] at h₁
  simp only [derivedAdjunction, mapDerivedCategoryRightDerivedAdjunction, derived_unit,
    ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app, Iso.symm_hom, assoc]
  rw [← h₃]
  simp only [Functor.map_comp, id_comp]
  rw [h₁, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, id_comp, h₂]

end CategoryTheory.Adjunction
