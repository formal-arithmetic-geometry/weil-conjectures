/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Defs

/-!
# Base change of the trait data

Let `R₀ → A₁` be a ring map, `B` an `R₀`-algebra, `B_K` the localization of `B` at the image of
the nonzero elements of `R₀` and `B₁ = B ⊗[R₀] A₁` (an `A₁`-algebra through the second factor).
If every nonzero element of `A₁` divides the image of a nonzero element of `R₀`, then
`B₁ ⊗[B] B_K` is the localization of `B₁` at the nonzero elements of `A₁`
(`Algebra.TraitSection.isLocalization_tensor_of_dvd`).

This is part of the reduction of the trait case of blueprint
`sbc-thm-spreading-finite-etale-galois` ([Stacks 0EYJ]) to a base containing the roots of unity.
-/

@[expose] public section

open TensorProduct

namespace Algebra.TraitSection

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- See the module docstring. -/
theorem isLocalization_tensor_of_dvd {R₀ A₁ B Bk : Type*} [CommRing R₀] [CommRing A₁]
    [Algebra R₀ A₁] [CommRing B] [Algebra R₀ B] [CommRing Bk] [Algebra B Bk]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) Bk]
    (hdvd : ∀ a ∈ nonZeroDivisors A₁, ∃ r ∈ nonZeroDivisors R₀, a ∣ algebraMap R₀ A₁ r)
    (hR : ∀ r ∈ nonZeroDivisors R₀, algebraMap R₀ A₁ r ∈ nonZeroDivisors A₁) :
    IsLocalization (Algebra.algebraMapSubmonoid (B ⊗[R₀] A₁) (nonZeroDivisors A₁))
      ((B ⊗[R₀] A₁) ⊗[B] Bk) := by
  have hmap (r : R₀) : algebraMap B (B ⊗[R₀] A₁) (algebraMap R₀ B r) =
      algebraMap A₁ (B ⊗[R₀] A₁) (algebraMap R₀ A₁ r) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.right_algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  refine IsLocalization.of_le_of_exists_dvd
    (Algebra.algebraMapSubmonoid (B ⊗[R₀] A₁)
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀))) _ ?_ ?_
  · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨_, hR r hr, (hmap r).symm⟩
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨r, hr, hdv⟩ := hdvd a ha
    exact ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, by rw [hmap]; exact map_dvd _ hdv⟩

end Algebra.TraitSection
