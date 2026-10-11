/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.Trace.Defs
public import WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# The classical Fourier transform on a finite field

Let `ψ` be an additive character of a field `K` and `L` a finite extension of `K`, for instance
`K = 𝔽_q` and `L = 𝔽_{qⁿ}`. The character `ψ_L = ψ ∘ Tr_{L/K}` of `L` defines the classical
Fourier transform of functions `f : L → R`,

`f̂(y) = ∑_{x ∈ L} f(x) ψ(Tr_{L/K}(x y))`.

By the Fourier trace formula, it is the function-theoretic model of the Fourier–Deligne
transform: up to sign, the trace function of the Fourier–Deligne transform of a Weil complex on
the affine line is the classical Fourier transform of its trace function. The two numerical
identities of the Fourier–Deligne transform, Plancherel and trace-level Fourier inversion, are
consequences of the corresponding identities for `f ↦ f̂` proved here, which in turn follow
from the orthogonality relations `AddChar.sum_compTrace_sub_mul`.

## Main declarations

- `FiniteField.fourierTransform`: the classical Fourier transform `f ↦ f̂` with respect to
  `ψ ∘ Tr_{L/K}`.

## Main statements

- `FiniteField.fourierTransform_inv_fourierTransform`: classical Fourier inversion,
  `(f̂)^∨ = #L · f`, the second transform taken with respect to `ψ⁻¹`.
- `FiniteField.sum_norm_sq_fourierTransform`: the classical Plancherel identity
  `∑_y |ι f̂(y)|² = #L ∑_x |ι f(x)|²` for an embedding `ι` of the values into `ℂ`.
-/

@[expose] public section

open ComplexConjugate

namespace FiniteField

variable {K L R : Type*} [Field K] [Field L] [Fintype L] [Algebra K L] [CommRing R]

/-- The *classical Fourier transform* `f̂(y) = ∑ₓ f(x) ψ(Tr_{L/K}(x y))` of a function
`f : L → R` on a finite field `L`, with respect to the additive character `ψ ∘ Tr_{L/K}` of `L`
induced by an additive character `ψ` of a subfield `K`. For `L = 𝔽_{qⁿ}` over `K = 𝔽_q` this
is the transform with respect to the character `ψₙ` of `𝔽_{qⁿ}`.
(sketch blueprint: `sk-def-trace`) -/
noncomputable def fourierTransform (ψ : AddChar K R) (f : L → R) (y : L) : R :=
  ∑ x, f x * ψ (Algebra.trace K L (x * y))

lemma fourierTransform_eq_sum_compTrace (ψ : AddChar K R) (f : L → R) (y : L) :
    fourierTransform ψ f y = ∑ x, f x * ψ.compTrace L (x * y) :=
  rfl

variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsDomain R]

/-- **Classical Fourier inversion.** For a nontrivial additive character `ψ` of `K`, the
transform with respect to `ψ⁻¹` of the transform with respect to `ψ` is `#L` times the
identity: `∑_x (∑_z f(z) ψ_L(z x)) ψ_L(-x y) = #L · f(y)`.
(sketch blueprint: `sk-prop-double-trace`, proof) -/
theorem fourierTransform_inv_fourierTransform {ψ : AddChar K R} (hψ : ψ ≠ 1) (f : L → R)
    (y : L) :
    fourierTransform ψ⁻¹ (fourierTransform ψ f) y = Fintype.card L * f y := by
  classical
  have h (z : L) : ∑ x, f z * ψ.compTrace L (z * x) * ψ⁻¹.compTrace L (x * y) =
      f z * ∑ x, ψ.compTrace L ((z - y) * x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [mul_assoc, AddChar.compTrace_apply, AddChar.compTrace_apply, AddChar.inv_apply,
      ← AddChar.map_add_eq_mul, ← map_neg, ← map_add, AddChar.compTrace_apply]
    congr 3
    ring
  simp_rw [fourierTransform_eq_sum_compTrace, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [h, AddChar.sum_compTrace_sub_mul hψ, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ y, if_pos (Finset.mem_univ _), mul_comm]

omit [Fintype L] [Algebra.IsSeparable K L] [IsDomain R] in
/-- The values of an additive character of a finite field, embedded in `ℂ`, are roots of
unity, so complex conjugation inverts them. -/
lemma conj_ringHom_compTrace [Finite K] (ι : R →+* ℂ) (ψ : AddChar K R) (t : L) :
    conj (ι (ψ.compTrace L t)) = ι (ψ.compTrace L (-t)) := by
  have : Finite L := Module.finite_of_finite K
  let := Fintype.ofFinite L
  have hpow : ι (ψ.compTrace L t) ^ Fintype.card L = 1 := by
    rw [← map_pow, ← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one,
      map_one]
  have hnorm := Complex.norm_eq_one_of_pow_eq_one hpow Fintype.card_ne_zero
  rw [← Complex.inv_eq_conj hnorm]
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← map_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, map_one]

/-- **Classical Plancherel identity.** For a nontrivial additive character `ψ` of a finite field
`K`, a finite extension `L / K` and a ring homomorphism `ι : R →+* ℂ`,
`∑_y |ι f̂(y)|² = #L ∑_x |ι f(x)|²`.
(sketch blueprint: `sk-cor-plancherel`, proof) -/
theorem sum_norm_sq_fourierTransform [Finite K] (ι : R →+* ℂ) {ψ : AddChar K R} (hψ : ψ ≠ 1)
    (f : L → R) :
    ∑ y, ‖ι (fourierTransform ψ f y)‖ ^ 2 = Fintype.card L * ∑ x, ‖ι (f x)‖ ^ 2 := by
  classical
  set g : L → ℂ := fun x ↦ ι (f x)
  set e : L → ℂ := fun t ↦ ι (ψ.compTrace L t)
  have hf (y : L) : ι (fourierTransform ψ f y) = ∑ x, g x * e (x * y) := by
    simp [fourierTransform_eq_sum_compTrace, g, e]
  have horth (x x' : L) :
      ∑ y, e ((x - x') * y) = if x = x' then (Fintype.card L : ℂ) else 0 := by
    simp only [e]
    rw [← map_sum, AddChar.sum_compTrace_sub_mul hψ]
    split_ifs <;> simp
  have hy (y : L) : ι (fourierTransform ψ f y) * conj (ι (fourierTransform ψ f y)) =
      ∑ x, ∑ x', g x * conj (g x') * e ((x - x') * y) := by
    rw [hf, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun x' _ ↦ ?_
    simp only [e]
    rw [map_mul (starRingEnd ℂ), conj_ringHom_compTrace,
      show (x - x') * y = x * y + -(x' * y) by ring, AddChar.map_add_eq_mul, map_mul ι]
    ring
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow,
    ← Complex.mul_conj', hy]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun x _ ↦ Finset.sum_comm).trans ?_
  simp_rw [← Finset.mul_sum, horth, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

end FiniteField
