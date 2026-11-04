/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.NumberTheory.Padics.CoefficientExtension

/-!
# The finite p-adic coefficient rings are `l`-primary

The prime `l` lies in the maximal ideal of `𝒪_E`, so `lⁿ` kills `A_{E,n} = 𝒪_E / ϖ_Eⁿ 𝒪_E`
(`Padic.pow_nsmul_coefficientExtensionRing`).

Source: Serre, Local Fields, Chapter II, §2 (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

namespace Padic

/-- The prime `l` lies in the maximal ideal `𝔪_E` of `𝒪_E`, since `|l|_E = |l|_l = l⁻¹ < 1`.

Source: Serre, Local Fields, Chapter II, §2 (auxiliary; not a blueprint node). -/
theorem natCast_mem_coefficientExtensionMaximalIdeal
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    (l : coefficientExtensionIntegers l E) ∈ coefficientExtensionMaximalIdeal l E := by
  have h := (coefficientExtensionIntegers_dvr l E).choose_spec
  rw [coefficientExtensionMaximalIdeal, h.2.1, Subring.coe_natCast,
    coefficientExtensionAbsoluteValue_apply, ← map_natCast (algebraMap ℚ_[l] E),
    spectralNorm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

/-- The power `lⁿ` lies in the ideal `ϖ_Eⁿ 𝒪_E` defining `A_{E,n}`.

Source: Serre, Local Fields, Chapter II, §2 (auxiliary; not a blueprint node). -/
theorem natCast_pow_mem_coefficientExtensionIdeal
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    (l : coefficientExtensionIntegers l E) ^ n ∈ coefficientExtensionIdeal l E n := by
  have hgen : Ideal.span ({coefficientExtensionUniformizer l E} :
      Set (coefficientExtensionIntegers l E)) = coefficientExtensionMaximalIdeal l E :=
    (coefficientExtensionIntegers_dvr l E).choose_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  rw [coefficientExtensionIdeal, hgen]
  exact Ideal.pow_mem_pow (natCast_mem_coefficientExtensionMaximalIdeal l E) n

/-- The coefficient ring `A_{E,n}` is killed by `lⁿ`.

Source: Serre, Local Fields, Chapter II, §2 (auxiliary; not a blueprint node). -/
theorem pow_nsmul_coefficientExtensionRing
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (a : coefficientExtensionRing l E n) :
    (l ^ n) • a = 0 := by
  rw [nsmul_eq_mul, Nat.cast_pow, ← map_natCast (Ideal.Quotient.mk _), ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem.mpr (natCast_pow_mem_coefficientExtensionIdeal l E n),
    zero_mul]

end Padic
