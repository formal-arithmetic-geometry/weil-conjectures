/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Invertible objects of a monoidal category

An object `M` of a monoidal category `C` is *invertible* when there is an object `N` together
with isomorphisms `M ⊗ N ≅ 𝟙_ C` and `N ⊗ M ≅ 𝟙_ C`. This file records two consequences of
invertibility:

* tensoring on the right by an invertible object is an equivalence of categories, and
* a morphism `𝟙_ C ⟶ M` to an invertible object which is a split monomorphism is an
  isomorphism.

The second is the categorical form of the fact that a surjective linear map onto an invertible
module over a commutative ring is bijective (`Module.Invertible.bijective_of_surjective`): every
endomorphism of `M` is multiplication by an endomorphism of `𝟙_ C`, and multiplication by a
scalar commutes with every morphism out of `𝟙_ C`, so a one-sided inverse is a two-sided
inverse.

## Main results

- `CategoryTheory.MonoidalCategory.tensorRightEquivalence`: tensoring on the right by an
  invertible object is an equivalence of categories.
- `CategoryTheory.MonoidalCategory.isIso_of_invertible_of_comp_eq_id`: a split monomorphism
  from the tensor unit to an invertible object is an isomorphism.

-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

open Category

variable {C : Type*} [Category* C] [MonoidalCategory C] {M N : C}

/-- Tensoring on the right by an invertible object is an equivalence of categories. -/
@[simps! functor inverse]
noncomputable def tensorRightEquivalence (e : M ⊗ N ≅ 𝟙_ C) (e' : N ⊗ M ≅ 𝟙_ C) : C ≌ C :=
  .mk (tensorRight M) (tensorRight N)
    ((rightUnitorNatIso C).symm ≪≫ ((tensoringRight C).mapIso e).symm ≪≫ tensorRightTensor M N)
    ((tensorRightTensor N M).symm ≪≫ (tensoringRight C).mapIso e' ≪≫ rightUnitorNatIso C)

/-- Every endomorphism `φ` of the tensor unit acts on an object `M` as the endomorphism
`(λ_ M).inv ≫ φ ▷ M ≫ (λ_ M).hom` of `M`, and this action commutes with every morphism
`ψ : 𝟙_ C ⟶ M`:

```
𝟙_ C ---- ψ ----> M
  |               |
  φ               (λ_ M).inv ≫ φ ▷ M ≫ (λ_ M).hom
  v               v
𝟙_ C ---- ψ ----> M
```
-/
lemma comp_eq_comp_leftUnitor_inv_whiskerRight (φ : 𝟙_ C ⟶ 𝟙_ C) (ψ : 𝟙_ C ⟶ M) :
    φ ≫ ψ = ψ ≫ (λ_ M).inv ≫ φ ▷ M ≫ (λ_ M).hom := by
  have key : (ρ_ (𝟙_ C)).inv ≫ 𝟙_ C ◁ ψ = ψ ≫ (λ_ M).inv := by
    rw [← cancel_mono (λ_ M).hom, assoc, assoc, Iso.inv_hom_id, comp_id,
      leftUnitor_naturality, ← assoc, unitors_equal, Iso.inv_hom_id, id_comp]
  calc φ ≫ ψ = φ ≫ ((ρ_ (𝟙_ C)).inv ≫ 𝟙_ C ◁ ψ) ≫ (λ_ M).hom := by
        rw [key]
        simp
    _ = ((ρ_ (𝟙_ C)).inv ≫ φ ▷ 𝟙_ C ≫ 𝟙_ C ◁ ψ) ≫ (λ_ M).hom := by
        simp only [← assoc, rightUnitor_inv_naturality]
    _ = ((ρ_ (𝟙_ C)).inv ≫ 𝟙_ C ◁ ψ ≫ φ ▷ M) ≫ (λ_ M).hom := by rw [whisker_exchange]
    _ = ψ ≫ (λ_ M).inv ≫ φ ▷ M ≫ (λ_ M).hom := by
        rw [← assoc, key]
        simp

/-- **A split monomorphism from the tensor unit to an invertible object is an isomorphism.**
Invertibility of `M` is recorded by an object `N` together with isomorphisms `M ⊗ N ≅ 𝟙_ C` and
`N ⊗ M ≅ 𝟙_ C`. -/
lemma isIso_of_invertible_of_comp_eq_id (e : M ⊗ N ≅ 𝟙_ C) (e' : N ⊗ M ≅ 𝟙_ C) {f : 𝟙_ C ⟶ M}
    {s : M ⟶ 𝟙_ C} (h : f ≫ s = 𝟙 _) : IsIso f := by
  have : (tensorRight M).IsEquivalence := (tensorRightEquivalence e e').isEquivalence_functor
  obtain ⟨w, hw⟩ := (tensorRight M).map_surjective ((λ_ M).hom ≫ s ≫ f ≫ (λ_ M).inv)
  simp only [Functor.flip_obj_obj, curriedTensor_obj_obj, Functor.flip_obj_map,
    curriedTensor_map_app] at hw
  have hw' : (λ_ M).inv ≫ w ▷ M ≫ (λ_ M).hom = s ≫ f := by
    rw [hw]
    simp
  have h₁ : w ≫ f = f := by
    rw [comp_eq_comp_leftUnitor_inv_whiskerRight w f, hw', ← assoc, h, id_comp]
  have h₂ : w = 𝟙 _ := by
    conv_lhs => rw [← comp_id w, ← h, ← assoc, h₁]
    exact h
  refine ⟨s, h, ?_⟩
  rw [← hw', h₂]
  simp

end CategoryTheory.MonoidalCategory
