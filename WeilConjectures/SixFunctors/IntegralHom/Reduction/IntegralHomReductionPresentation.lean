/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionComponents
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionNormalization

/-! # One normalized integral reduction presentation

We show that a normalized reduction presentation exists at each fixed quotient level; this is
the fixed-level coefficient-extension step in the construction of integral Hom models.

## Implementation details

Ordinary scalar extension and restriction have unit `x ↦ 1 ⊗ x`. Balanced tensor
associativity identifies the comparison with multiplication of coefficient factors, and the
left-derived universal property applied to the same source tensor presentation gives the
counit square, which is the normalization field of `ReductionPresentation`.

## References

* Stacks Project, Tags 07A4, 07A6.
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

/-- A normalized reduction presentation of `a` exists at each fixed quotient level `n`. -/
theorem reduction_presentation_exists_at
    (a : TensorPresentation.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) (n : ℕ) :
    Nonempty (ReductionPresentation l E Y D hl a n) := by
  obtain ⟨target⟩ := reduction_target_exists l E Y n
  obtain ⟨m, _⟩ := reduction_normalization_exists l E Y D hl a n target
  exact ⟨m⟩

end WeilConjectures.IntegralHom
