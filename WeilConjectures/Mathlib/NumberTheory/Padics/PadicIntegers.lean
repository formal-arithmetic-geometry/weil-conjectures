/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# `ℓ`-adic numbers as fractions of `ℓ`-adic integers

Every `ℓ`-adic number is of the form `ℓ ^ (-b) * z` with `z` an `ℓ`-adic integer, that is,
`ℚ_[ℓ] = ℤ_[ℓ][1/ℓ]`.
-/

@[expose] public section

namespace Padic

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- Every `ℓ`-adic number is of the form `ℓ ^ (-b) * z` with `z` an `ℓ`-adic integer, that is,
`ℚ_[ℓ] = ℤ_[ℓ][1/ℓ]`. -/
theorem exists_eq_inv_pow_mul (q : ℚ_[ℓ]) :
    ∃ (b : ℕ) (z : ℤ_[ℓ]), q = ((ℓ : ℚ_[ℓ]) ^ b)⁻¹ * z := by
  obtain ⟨⟨z, d⟩, hzd⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[ℓ]) q
  have hd : (d : ℤ_[ℓ]) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hspec := PadicInt.unitCoeff_spec hd
  set u := PadicInt.unitCoeff hd
  refine ⟨(d : ℤ_[ℓ]).valuation, z * ↑u⁻¹, ?_⟩
  generalize (d : ℤ_[ℓ]).valuation = v at hspec ⊢
  have hℓ : (ℓ : ℚ_[ℓ]) ^ v ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne ℓ))
  have hu : ((u : ℤ_[ℓ]) : ℚ_[ℓ]) * ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1 := by
    rw [← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one]
  simp only [PadicInt.algebraMap_apply] at hzd
  rw [PadicInt.coe_mul, ← hzd, hspec, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
  calc q = q * (((u : ℤ_[ℓ]) : ℚ_[ℓ]) * ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) *
      ((ℓ : ℚ_[ℓ]) ^ v * ((ℓ : ℚ_[ℓ]) ^ v)⁻¹) := by
        rw [hu, mul_inv_cancel₀ hℓ, mul_one, mul_one]
    _ = _ := by ring

end Padic
