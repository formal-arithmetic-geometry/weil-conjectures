/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.NumberTheory.Padics.PadicNumbers

public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.RingTheory.Ideal.Quotient.Defs
/-!
# Finite p-adic coefficient extensions

We define the coefficient data of a finite extension `E / ℚ_l`: its absolute value, ring of
integers `𝒪_E`, maximal ideal `𝔪_E`, a uniformizer `ϖ_E`, and the finite coefficient rings
`A_{E,n} = 𝒪_E / ϖ_Eⁿ 𝒪_E` with their transition maps.

## Implementation details

The absolute value is the spectral absolute value, and the ring of integers is its closed unit
ball `{x : E | |x|_E ≤ 1}`; it is a subring because the spectral norm is nonarchimedean
(`isNonarchimedean_spectralNorm`). The maximal ideal and the uniformizer are chosen from
`extension_integers_dvr`. The ideal `coefficientExtensionIdeal` is `(span {ϖ_E})ⁿ`, which equals
`span {ϖ_Eⁿ}` by `Ideal.span_singleton_pow` and equals `𝔪_Eⁿ` since `ϖ_E` generates `𝔪_E`.
-/

@[expose] public section

universe u

namespace Padic

/-- The unique absolute value on `E` extending the p-adic absolute value, given by the
spectral norm. -/
noncomputable def coefficientExtensionAbsoluteValue (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    AbsoluteValue E ℝ :=
  MulRingNorm.mulRingNormEquivAbsoluteValue (spectralMulAlgNorm ℚ_[l] E).toMulRingNorm

/-- The coefficient absolute value is the spectral norm. -/
lemma coefficientExtensionAbsoluteValue_apply (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (x : E) :
    coefficientExtensionAbsoluteValue l E x = spectralNorm ℚ_[l] E x :=
  rfl

/-- The valuation ring `𝒪_E = {x : E | |x|_E ≤ 1}` of the spectral absolute value. -/
noncomputable def coefficientExtensionIntegers (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Subring E where
  carrier := {x | coefficientExtensionAbsoluteValue l E x ≤ 1}
  mul_mem' {a b} ha hb := by
    change coefficientExtensionAbsoluteValue l E (a * b) ≤ 1
    rw [map_mul]
    exact (mul_le_of_le_one_left (AbsoluteValue.nonneg _ b) ha).trans hb
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

namespace Padic

section

/-- The witness subring of `extension_integers_dvr` for the spectral absolute value is the
closed unit ball `coefficientExtensionIntegers l E`. -/
theorem coefficientExtensionIntegers_eq_choose (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    coefficientExtensionIntegers l E =
      (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
        (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose :=
  Subring.ext fun x ↦ (mem_coefficientExtensionIntegers l E x).trans
    ((extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.1 x).symm


/-- The conclusion of `extension_integers_dvr` for the spectral absolute value, stated for
the closed unit ball `coefficientExtensionIntegers l E` itself. -/
theorem coefficientExtensionIntegers_dvr (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ m : Ideal (coefficientExtensionIntegers l E),
      (∀ x : E, x ∈ coefficientExtensionIntegers l E ↔
        coefficientExtensionAbsoluteValue l E x ≤ 1) ∧
      (∀ x : coefficientExtensionIntegers l E, x ∈ m ↔
        coefficientExtensionAbsoluteValue l E (x : E) < 1) ∧
      (∀ x : coefficientExtensionIntegers l E, IsUnit x ↔
        coefficientExtensionAbsoluteValue l E (x : E) = 1) ∧
      IsLocalRing (coefficientExtensionIntegers l E) ∧ m.IsMaximal ∧
      (∀ J : Ideal (coefficientExtensionIntegers l E), J.IsMaximal → J = m) ∧
      IsFractionRing (coefficientExtensionIntegers l E) E ∧
      IsDiscreteValuationRing (coefficientExtensionIntegers l E) ∧
      IsPrincipalIdealRing (coefficientExtensionIntegers l E) ∧ m ≠ ⊥ ∧
      (∀ J : Ideal (coefficientExtensionIntegers l E), J.IsPrime ∧ J ≠ ⊥ ↔ J = m) ∧
      Finite (coefficientExtensionIntegers l E ⧸ m) ∧
      (∃ r : ℝ,
        (∃ y : coefficientExtensionIntegers l E, y ∈ m ∧ y ≠ 0 ∧
          coefficientExtensionAbsoluteValue l E (y : E) = r) ∧
        (∀ y : coefficientExtensionIntegers l E, y ∈ m → y ≠ 0 →
          coefficientExtensionAbsoluteValue l E (y : E) ≤ r) ∧
        (∀ π : coefficientExtensionIntegers l E,
          Ideal.span ({π} : Set (coefficientExtensionIntegers l E)) = m ↔
            π ≠ 0 ∧ coefficientExtensionAbsoluteValue l E (π : E) = r)) ∧
      (∃ π : coefficientExtensionIntegers l E,
        Ideal.span ({π} : Set (coefficientExtensionIntegers l E)) = m) ∧
      (∀ π π' : coefficientExtensionIntegers l E,
        Ideal.span ({π} : Set (coefficientExtensionIntegers l E)) = m →
        Ideal.span ({π'} : Set (coefficientExtensionIntegers l E)) = m →
          ∃ v : (coefficientExtensionIntegers l E)ˣ,
            π' = (v : coefficientExtensionIntegers l E) * π) ∧
      (∀ π : coefficientExtensionIntegers l E,
        Ideal.span ({π} : Set (coefficientExtensionIntegers l E)) = m → ∀ x : Eˣ,
        ∃! p : (coefficientExtensionIntegers l E)ˣ × ℤ,
          (x : E) = ((p.1 : coefficientExtensionIntegers l E) : E) * (π : E) ^ p.2) := by
  obtain ⟨O, hO⟩ := extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))
  obtain rfl : O = coefficientExtensionIntegers l E :=
    Subring.ext fun x ↦ (hO.choose_spec.1 x).trans (mem_coefficientExtensionIntegers l E x).symm
  exact hO

/-- The maximal ideal `𝔪_E = {x : 𝒪_E | |x|_E < 1}`. -/
noncomputable def coefficientExtensionMaximalIdeal (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Ideal (coefficientExtensionIntegers l E) :=
  (coefficientExtensionIntegers_dvr l E).choose

/-- A chosen uniformizer `ϖ_E`, generating `𝔪_E`. -/
noncomputable def coefficientExtensionUniformizer (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    coefficientExtensionIntegers l E :=
  (coefficientExtensionIntegers_dvr l E).choose_spec
    |>.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose

/-- The ideal `ϖ_Eⁿ 𝒪_E = 𝔪_Eⁿ`, defined as `(span {ϖ_E})ⁿ`. -/
noncomputable def coefficientExtensionIdeal (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Ideal (coefficientExtensionIntegers l E) :=
  Ideal.span ({coefficientExtensionUniformizer l E} :
    Set (coefficientExtensionIntegers l E)) ^ n

/-- The finite coefficient ring `A_{E,n} = 𝒪_E / ϖ_Eⁿ 𝒪_E` (the zero ring at `n = 0`). -/
@[reducible]
noncomputable def coefficientExtensionRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Type u :=
  coefficientExtensionIntegers l E ⧸ coefficientExtensionIdeal l E n

/-- The surjective transition homomorphism `A_{E,n+1} → A_{E,n}`, induced by the identity
on `𝒪_E`. -/
noncomputable def coefficientExtensionTransition (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    coefficientExtensionRing l E (n + 1) →+* coefficientExtensionRing l E n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))

end

end Padic
