/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.NumberTheory.Padics.CoefficientExtension
import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Finiteness interface for finite p-adic coefficient extensions

Source: Weil blueprint, `def-weil-finite-field-fiber`, order 411;
Serre, Local Fields, Chapter II, §2
(auxiliary; not a blueprint node).

The coefficient constructions are imported unchanged; this supplies their finite-ring
interface at positive levels.
-/

@[expose] public section

universe u

namespace Padic

/-- The coefficient ring at a finite level is finite.

Source: Weil conjectures blueprint, node `def-weil-finite-field-fiber`,
order 411; Serre, Local Fields, Chapter II, §2
(auxiliary; not a blueprint node).

Proof: Apply `Padic.extension_integers_dvr` to the spectral absolute value to obtain
that the recorded integer ring is a DVR with finite residue field. Its recorded
uniformizer generates the recorded maximal ideal. Thus the ideal defining the level
`n` ring is the `n`th power of that maximal ideal. Each successive ideal quotient
is a finite-dimensional vector space over the finite residue field, and induction
on `n` gives the finiteness of the ring quotient. Equivalently apply
`Ideal.finite_quotient_pow` in the Noetherian integer ring after identifying ideals.
-/
theorem finite_coefficientExtensionRing
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n) :
    Finite (Padic.coefficientExtensionRing l E n) := by
  have h := (coefficientExtensionIntegers_dvr l E).choose_spec
  have hfinite : Finite (coefficientExtensionIntegers l E ⧸
      coefficientExtensionMaximalIdeal l E) :=
    h.2.2.2.2.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({coefficientExtensionUniformizer l E} :
      Set (coefficientExtensionIntegers l E)) = coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have : Finite (coefficientExtensionIntegers l E ⧸
      Ideal.span ({coefficientExtensionUniformizer l E} :
        Set (coefficientExtensionIntegers l E))) := by
    rw [hgen]
    exact hfinite
  exact Ideal.finite_quotient_pow (Submodule.fg_span_singleton _) n

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
