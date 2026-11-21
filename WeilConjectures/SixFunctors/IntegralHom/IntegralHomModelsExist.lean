/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralHomTensorPresentation
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionPresentation

/-! # Existence of normalized integral tensor-Hom models

## References

* [Stacks, Tag 06YS]
* [Stacks, Tag 06YU]
* [Stacks, Tag 08J9]
* [Stacks, Tag 08JA]
* [Stacks, Tag 07A4]
* [Stacks, Tag 07A6]
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- The ordinary uncompleted tensor and its coefficient comparisons admit the
normalizations specified by the existing presentation records. This statement does
not assert either internal-Hom reduction or preservation of completeness. -/
theorem models_exist :
    ∃ a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl),
      ∀ n : ℕ, Nonempty (ReductionPresentation l E Y D hl a n) := by
  obtain ⟨a⟩ := tensor_presentation_exists l E Y D hl
  exact ⟨a, fun n => reduction_presentation_exists_at l E Y D hl a n⟩

end WeilConjectures.IntegralHom
