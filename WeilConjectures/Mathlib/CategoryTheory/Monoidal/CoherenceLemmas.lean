/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Invertible objects of a monoidal category

An object `M` of a monoidal category is *invertible* when there is an object `N` together with
isomorphisms `M ⊗ N ≅ 𝟙_` and `N ⊗ M ≅ 𝟙_`. This file records four consequences of
invertibility:

* tensoring on the right by an invertible object is an equivalence of categories, hence in
  particular carries zero objects to zero objects and, being exact, short exact sequences to
  short exact sequences (`CategoryTheory.ShortComplex.ShortExact.map_of_exact`),
* a morphism `𝟙_ ⟶ M` to an invertible object which is a split monomorphism is an isomorphism,
* a tensor inverse of an object isomorphic to the tensor unit is itself isomorphic to the unit,
* two morphisms `𝟙_ ⟶ M` and `𝟙_ ⟶ N` out of the tensor unit have a **product**
  `CategoryTheory.MonoidalCategory.pairing`, an endomorphism of `𝟙_`, determined by a chosen
  isomorphism `e : M ⊗ N ≅ 𝟙_`.

The second is the categorical form of the fact that a surjective linear map onto an invertible
module over a commutative ring is bijective (`Module.Invertible.bijective_of_surjective`): every
endomorphism of `M` is multiplication by an endomorphism of `𝟙_`, and multiplication by a scalar
commutes with every morphism out of `𝟙_`, so a one-sided inverse is a two-sided inverse.

## Main definitions

- `CategoryTheory.MonoidalCategory.isoTensorUnitOfTensorIso`
- `CategoryTheory.MonoidalCategory.pairing`, with
  `CategoryTheory.MonoidalCategory.pairing_eq` rewriting it as a tensor product of the two
  factors.

## Main results

- `CategoryTheory.MonoidalCategory.tensorRightEquivalence`
- `CategoryTheory.MonoidalCategory.isZero_tensorObj_of_isZero`
- `CategoryTheory.MonoidalCategory.isIso_of_comp_eq_id`

-/

@[expose] public section

universe v u

namespace CategoryTheory.MonoidalCategory

open Category Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {M N : C}

/-- Tensoring on the right by an invertible object is an equivalence of categories. -/
@[simps! functor inverse]
noncomputable def tensorRightEquivalence (e : M ⊗ N ≅ 𝟙_ C) (e' : N ⊗ M ≅ 𝟙_ C) : C ≌ C :=
  .mk (tensorRight M) (tensorRight N)
    ((rightUnitorNatIso C).symm ≪≫ ((tensoringRight C).mapIso e).symm ≪≫ tensorRightTensor M N)
    ((tensorRightTensor N M).symm ≪≫ (tensoringRight C).mapIso e' ≪≫ rightUnitorNatIso C)

/-- **Tensoring on the right by an invertible object is an equivalence.** -/
lemma isEquivalence_tensorRight (e : M ⊗ N ≅ 𝟙_ C) (e' : N ⊗ M ≅ 𝟙_ C) :
    (tensorRight M).IsEquivalence :=
  (tensorRightEquivalence e e').isEquivalence_functor

/-- **Tensoring a zero object by an invertible object gives a zero object.** -/
lemma isZero_tensorObj_of_isZero [HasZeroMorphisms C] (e : M ⊗ N ≅ 𝟙_ C) (e' : N ⊗ M ≅ 𝟙_ C)
    {A : C} (hA : IsZero A) : IsZero (A ⊗ M) :=
  have : (tensorRight M).IsEquivalence := isEquivalence_tensorRight e e'
  (tensorRight M).map_isZero hA

/-- Every endomorphism `φ` of the tensor unit acts on an object `M` as an endomorphism of `M`,
and this action commutes with every morphism `𝟙_ ⟶ M`. -/
lemma comp_eq_comp_leftUnitor_conj (φ : 𝟙_ C ⟶ 𝟙_ C) (ψ : 𝟙_ C ⟶ M) :
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

/-- **A split monomorphism from the tensor unit to an invertible object is an isomorphism.** -/
lemma isIso_of_comp_eq_id (e : M ⊗ N ≅ 𝟙_ C) (e' : N ⊗ M ≅ 𝟙_ C) {f : 𝟙_ C ⟶ M}
    {s : M ⟶ 𝟙_ C} (h : f ≫ s = 𝟙 _) : IsIso f := by
  have := isEquivalence_tensorRight e e'
  obtain ⟨w, hw⟩ := (tensorRight M).map_surjective ((λ_ M).hom ≫ s ≫ f ≫ (λ_ M).inv)
  have hw' : (λ_ M).inv ≫ w ▷ M ≫ (λ_ M).hom = s ≫ f := by
    have h' : w ▷ M = (λ_ M).hom ≫ s ≫ f ≫ (λ_ M).inv := hw
    rw [h']
    simp
  have h₁ : w ≫ f = f := by
    rw [comp_eq_comp_leftUnitor_conj w f, hw', ← assoc, h, id_comp]
  have h₂ : w = 𝟙 _ := by
    conv_lhs => rw [← comp_id w, ← h, ← assoc, h₁]
    exact h
  refine ⟨s, h, ?_⟩
  rw [← hw', h₂]
  simp

/-- **A tensor inverse of an object isomorphic to the tensor unit is isomorphic to the unit**: for
`e : M ⊗ N ≅ 𝟙_ C` and `i : M ≅ 𝟙_ C`, the composite

```
        (λ_ N).symm        i.symm ▷ N          e
    N ─────────────→ 𝟙_ ⊗ N ─────────→ M ⊗ N ─────→ 𝟙_
```
-/
def isoTensorUnitOfTensorIso (e : M ⊗ N ≅ 𝟙_ C) (i : M ≅ 𝟙_ C) : N ≅ 𝟙_ C :=
  (λ_ N).symm ≪≫ (i.symm ⊗ᵢ Iso.refl N) ≪≫ e

/-- **The product of two morphisms out of the tensor unit** determined by an isomorphism
`e : M ⊗ N ≅ 𝟙_ C`: the composite

```
        g        (ρ_ M).inv        M ◁ h          e
   𝟙_ ─────→ M ──────────→ M ⊗ 𝟙_ ───────→ M ⊗ N ───→ 𝟙_
```

By `CategoryTheory.MonoidalCategory.pairing_eq` it is also `g ⊗ₘ h` read through the unitor and
`e`, which is the symmetric description. -/
def pairing (e : M ⊗ N ≅ 𝟙_ C) (g : 𝟙_ C ⟶ M) (h : 𝟙_ C ⟶ N) : 𝟙_ C ⟶ 𝟙_ C :=
  g ≫ (ρ_ M).inv ≫ (M ◁ h) ≫ e.hom

/-- **The product of two morphisms out of the tensor unit is their tensor product**, read through
the left unitor and `e`. -/
lemma pairing_eq (e : M ⊗ N ≅ 𝟙_ C) (g : 𝟙_ C ⟶ M) (h : 𝟙_ C ⟶ N) :
    pairing e g h = (λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h) ≫ e.hom := by
  rw [pairing, rightUnitor_inv_naturality_assoc, tensorHom_def, unitors_inv_equal]
  simp

end CategoryTheory.MonoidalCategory
