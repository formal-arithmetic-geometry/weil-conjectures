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

We show that a normalized tensor presentation over the completed integral coefficient ring exists
together with compatible reduction presentations at every finite level.

## Implementation details

The tensor is the localized signed total tensor of flat-term K-flat resolutions; for a
K-injective target, sectionwise currying identifies chain maps out of the total tensor with maps
into the Hom complex. The same construction is applied over every finite quotient: ordinary
scalar extension preserves K-flatness, and its total tensor comparison, inverse to
`s ⊗ (x ⊗ y) ↦ (s ⊗ x) ⊗ (1 ⊗ y)`, descends by the left-derived universal property of
reduction. The same source presentation is used for every `n`, and no boundedness is assumed.

## References

* Stacks Project, Tags 06YS, 06YU, 08J9, 08JA, 07A4, 07A6.
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

/-- There is a normalized tensor presentation over the completed integral coefficient ring
admitting a reduction presentation at every finite level `n`. This asserts neither internal-Hom
reduction nor preservation of completeness. -/
theorem models_exist :
    ∃ a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl),
      ∀ n : ℕ, Nonempty (ReductionPresentation l E Y D hl a n) := by
  obtain ⟨a⟩ := tensor_presentation_exists l E Y D hl
  exact ⟨a, fun n => reduction_presentation_exists_at l E Y D hl a n⟩

end WeilConjectures.IntegralHom
