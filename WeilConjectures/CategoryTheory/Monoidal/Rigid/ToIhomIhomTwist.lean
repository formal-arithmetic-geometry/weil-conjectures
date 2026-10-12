/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Twisting the dualizing object by an invertible object

In a braided monoidal closed category, the double-dual map `X ⟶ [[X, W], W]`
(`CategoryTheory.MonoidalClosed.toIhomIhom`) is an isomorphism if and only if the double-dual
map `X ⟶ [[X, W ⊗ N], W ⊗ N]` relative to the twisted object `W ⊗ N` is, for every invertible
object `N`: the twist cancels after dualizing twice.

## Main statements

- `CategoryTheory.MonoidalClosed.isIso_toIhomIhom_iff_bijective`: `toIhomIhom W X` is an
  isomorphism if and only if `f ↦ [f, W]` is a bijection `(T ⟶ X) ≃ ([X, W] ⟶ [T, W])` for all
  `T`.
- `CategoryTheory.MonoidalClosed.isIso_toIhomIhom_tensorObj_iff`: the twist invariance.
-/

@[expose] public section

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

section Braided

variable [BraidedCategory C]

/-- The double-dual map `X ⟶ [[X, W], W]` is an isomorphism if and only if precomposition
`f ↦ [f, W] : (T ⟶ X) → ([X, W] ⟶ [T, W])` is bijective for every object `T` (Yoneda): maps
`T ⟶ [[X, W], W]` correspond to maps `[X, W] ⟶ [T, W]`, and `f ≫ toIhomIhom W X` corresponds
to `[f, W]`. -/
lemma isIso_toIhomIhom_iff_bijective (W X : C) :
    IsIso (toIhomIhom W X) ↔
      ∀ T : C, Function.Bijective (fun f : T ⟶ X ↦ (pre f).app W) := by
  rw [isIso_iff_yoneda_map_bijective]
  refine forall_congr' fun T ↦ ?_
  let e : (T ⟶ (ihom ((ihom X).obj W)).obj W) ≃ ((ihom X).obj W ⟶ (ihom T).obj W) :=
    { toFun g := curry ((β_ _ T).inv ≫ uncurry g)
      invFun h := curry ((β_ _ T).hom ≫ uncurry h)
      left_inv g := by simp
      right_inv h := by simp }
  have h : (fun f : T ⟶ X ↦ (pre f).app W) = e ∘ (fun f ↦ f ≫ toIhomIhom W X) := by
    ext1 f
    dsimp [e]
    rw [uncurry_natural_left, uncurry_toIhomIhom,
      ← BraidedCategory.braiding_inv_naturality_left_assoc, Iso.inv_hom_id_assoc,
      ← uncurry_pre, curry_uncurry]
  rw [h, e.bijective.of_comp_iff']

/-- **Twisting the dualizing object by an invertible object.** In a braided monoidal closed
category, for an invertible object `N`, the double-dual map `X ⟶ [[X, W ⊗ N], W ⊗ N]` is an
isomorphism if and only if `X ⟶ [[X, W], W]` is: the comparison isomorphisms
`[A, W] ⊗ N ≅ [A, W ⊗ N]` (`CategoryTheory.MonoidalClosed.isIso_ihomTensorToIhom`) are natural
in `A`, and `- ⊗ N` is fully faithful. -/
theorem isIso_toIhomIhom_tensorObj_iff (W X : C) {N : C} (hN : IsInvertible N) :
    IsIso (toIhomIhom (W ⊗ N) X) ↔ IsIso (toIhomIhom W X) := by
  rw [isIso_toIhomIhom_iff_bijective, isIso_toIhomIhom_iff_bijective]
  refine forall_congr' fun T ↦ ?_
  have := isIso_ihomTensorToIhom X W hN
  have := isIso_ihomTensorToIhom T W hN
  obtain ⟨N', ⟨e⟩, ⟨e'⟩⟩ := hN
  let E := tensorRightEquivalenceOfTensorIso e e'
  have h : (fun f : T ⟶ X ↦ (pre f).app (W ⊗ N)) =
      ((asIso (ihomTensorToIhom X W N)).homCongr (asIso (ihomTensorToIhom T W N)) ∘
        fun g ↦ g ▷ N) ∘ fun f ↦ (pre f).app W := by
    ext1 f
    simp [Iso.homCongr_apply, pre_app_whiskerRight_comp_ihomTensorToIhom]
  rw [h, Function.Bijective.of_comp_iff']
  exact (Equiv.bijective _).comp (E.fullyFaithfulFunctor.map_bijective _ _)

end Braided

end CategoryTheory.MonoidalClosed
