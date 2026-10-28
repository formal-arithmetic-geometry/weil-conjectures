/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Finite p-adic coefficient extensions

Source: Weil conjectures blueprint, `def-weil-finite-field-fiber`, order 411;
slopmaster2, Definition `def:weil-finite-coefficient-datum`
(auxiliary; not a blueprint node).

The absolute value is the spectral absolute value, and the ring of integers is its closed unit
ball `{x : E | |x|_E ≤ 1}`; it is a subring because the spectral norm is nonarchimedean
(`isNonarchimedean_spectralNorm`).
-/

@[expose] public section

universe u

namespace Padic

/-- The unique absolute value extending the p-adic absolute value, given by the spectral norm.
Its uniqueness, nonarchimedean property and completeness are the cited Mathlib facts.

Source: blueprint `def-weil-finite-field-fiber`, order 411, and slopmaster2 Definition
`def:weil-finite-coefficient-datum` (auxiliary; not a blueprint node). -/
noncomputable def coefficientExtensionAbsoluteValue (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    AbsoluteValue E ℝ :=
  MulRingNorm.mulRingNormEquivAbsoluteValue (spectralMulAlgNorm ℚ_[l] E).toMulRingNorm

/-- The coefficient absolute value is the spectral norm. -/
lemma coefficientExtensionAbsoluteValue_apply (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (x : E) :
    coefficientExtensionAbsoluteValue l E x = spectralNorm ℚ_[l] E x :=
  rfl

/-- The valuation ring `𝒪_E = {x : E | |x|_E ≤ 1}` of the spectral absolute value.

Source: blueprint `def-weil-finite-field-fiber`, order 411, and slopmaster2 Definition
`def:weil-finite-coefficient-datum` (auxiliary; not a blueprint node). -/
noncomputable def coefficientExtensionIntegers (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Subring E where
  carrier := {x | coefficientExtensionAbsoluteValue l E x ≤ 1}
  mul_mem' {a b} ha hb := by
    change coefficientExtensionAbsoluteValue l E (a * b) ≤ 1
    rw [map_mul]
    exact mul_le_one₀ ha (AbsoluteValue.nonneg _ b) hb
  one_mem' := by simp
  add_mem' {a b} ha hb :=
    (isNonarchimedean_spectralNorm (K := ℚ_[l]) (L := E) a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by
    change coefficientExtensionAbsoluteValue l E (-a) ≤ 1
    rwa [AbsoluteValue.map_neg]

/-- Membership in `𝒪_E` is absolute value at most one. -/
lemma mem_coefficientExtensionIntegers (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (x : E) :
    x ∈ coefficientExtensionIntegers l E ↔ coefficientExtensionAbsoluteValue l E x ≤ 1 :=
  Iff.rfl

end Padic
