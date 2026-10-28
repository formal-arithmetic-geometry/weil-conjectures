/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FourierTransform.Classical

/-!
# The classical Fourier transform on a finite affine space

Let `ψ` be an additive character of a field `K`, `L` a finite extension of `K` and `ι` a finite
index type, for instance `K = 𝔽_q`, `L = 𝔽_{qⁿ}` and `#ι = r`. The character
`ψ_L = ψ ∘ Tr_{L/K}` and the standard pairing `⟨x, y⟩ = ∑ᵢ xᵢ yᵢ` of `L^ι` define the classical
Fourier transform of functions `f : L^ι → R`,

`f̂(y) = ∑_{x ∈ L^ι} f(x) ψ(Tr_{L/K}⟨x, y⟩)`.

It is the function-theoretic model of the Fourier–Deligne transform on the affine space
`𝔸^ι`; for `ι` with one element it is `FiniteField.fourierTransform`. The orthogonality
relations on `L^ι` are the product over `ι` of the orthogonality relations
`AddChar.sum_compTrace_sub_mul` on `L`, and Fourier inversion and the Plancherel identity follow
as on `L`, with `#L` replaced by `#L ^ #ι`.

## Main declarations

- `FiniteField.fourierTransformPi`: the classical Fourier transform `f ↦ f̂` on `L^ι` with
  respect to `ψ ∘ Tr_{L/K}`.

## Main statements

- `FiniteField.sum_compTrace_sum_sub_mul`: orthogonality of the characters
  `y ↦ ψ(Tr⟨x, y⟩)` of `L^ι`.
- `FiniteField.fourierTransformPi_inv_fourierTransformPi`: classical Fourier inversion,
  `(f̂)^∨ = #L ^ #ι · f`, the second transform taken with respect to `ψ⁻¹`.
- `FiniteField.sum_norm_sq_fourierTransformPi`: the classical Plancherel identity
  `∑_y |ι f̂(y)|² = #L ^ #ι ∑_x |ι f(x)|²` for an embedding of the values into `ℂ`.
-/

@[expose] public section

open ComplexConjugate

namespace FiniteField

variable {K L R ι : Type*} [Field K] [Field L] [Fintype L] [Algebra K L] [CommRing R]
  [Fintype ι] [DecidableEq ι]

/-- The *classical Fourier transform* `f̂(y) = ∑ₓ f(x) ψ(Tr_{L/K}⟨x, y⟩)` of a function
`f : L^ι → R` on a finite affine space, `⟨x, y⟩ = ∑ᵢ xᵢ yᵢ` being the standard pairing, with
respect to the additive character `ψ ∘ Tr_{L/K}` of `L` induced by an additive character `ψ` of a
subfield `K`. (sketch blueprint: `def-fd-trace-function`) -/
noncomputable def fourierTransformPi (ψ : AddChar K R) (f : (ι → L) → R) (y : ι → L) : R :=
  ∑ x, f x * ψ (Algebra.trace K L (∑ i, x i * y i))

lemma fourierTransformPi_eq_sum_compTrace (ψ : AddChar K R) (f : (ι → L) → R) (y : ι → L) :
    fourierTransformPi ψ f y = ∑ x, f x * ψ.compTrace L (∑ i, x i * y i) :=
  rfl

/-- The classical Fourier transform on `L^ι` commutes with negation. -/
lemma fourierTransformPi_neg (ψ : AddChar K R) (f : (ι → L) → R) :
    fourierTransformPi ψ (fun x ↦ -f x) = fun y ↦ -fourierTransformPi ψ f y := by
  ext y
  simp [fourierTransformPi]

/-- The classical Fourier transform on `L^ι` is linear over the constants. -/
lemma fourierTransformPi_const_mul (ψ : AddChar K R) (c : R) (f : (ι → L) → R) (y : ι → L) :
    fourierTransformPi ψ (fun x ↦ c * f x) y = c * fourierTransformPi ψ f y := by
  simp [fourierTransformPi, Finset.mul_sum, mul_assoc]

variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsDomain R]

/-- **Additive orthogonality on `L^ι`.** For a nontrivial additive character `ψ` of `K`,
`∑_{y ∈ L^ι} ψ_L(⟨x - x', y⟩) = #L ^ #ι` if `x = x'` and `0` otherwise: the sum is the product
over `ι` of the orthogonality relations on `L`.
(blueprint: `lem-fd-additive-orthogonality`; sketch blueprint: `lem-fd-additive-orthogonality`) -/
theorem sum_compTrace_sum_sub_mul [DecidableEq L] {ψ : AddChar K R} (hψ : ψ ≠ 1) (x x' : ι → L) :
    ∑ y : ι → L, ψ.compTrace L (∑ i, (x i - x' i) * y i) =
      if x = x' then (Fintype.card L : R) ^ Fintype.card ι else 0 := by
  classical
  have hprod (t : ι → L) : ψ.compTrace L (∑ i, t i) = ∏ i, ψ.compTrace L (t i) := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha,
        AddChar.map_add_eq_mul, ih]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun i (t : L) ↦ ψ.compTrace L ((x i - x' i) * t))]
  simp_rw [AddChar.sum_compTrace_sub_mul hψ]
  split_ifs with h
  · simp [h]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- **Classical Fourier inversion on `L^ι`.** For a nontrivial additive character `ψ` of `K`,
the transform with respect to `ψ⁻¹` of the transform with respect to `ψ` is `#L ^ #ι` times
the identity. (sketch blueprint: `det-prop-double-trace`, proof) -/
theorem fourierTransformPi_inv_fourierTransformPi {ψ : AddChar K R} (hψ : ψ ≠ 1)
    (f : (ι → L) → R) (y : ι → L) :
    fourierTransformPi ψ⁻¹ (fourierTransformPi ψ f) y =
      (Fintype.card L : R) ^ Fintype.card ι * f y := by
  classical
  have h (z : ι → L) : ∑ x : ι → L, f z * ψ.compTrace L (∑ i, z i * x i) *
      ψ⁻¹.compTrace L (∑ i, x i * y i) =
      f z * ∑ x : ι → L, ψ.compTrace L (∑ i, (z i - y i) * x i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [mul_assoc, AddChar.compTrace_apply, AddChar.compTrace_apply, AddChar.inv_apply,
      ← AddChar.map_add_eq_mul, ← map_neg, ← map_add, AddChar.compTrace_apply]
    congr 3
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  simp_rw [fourierTransformPi_eq_sum_compTrace, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [h, sum_compTrace_sum_sub_mul hψ, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ y, if_pos (Finset.mem_univ _), mul_comm]

/-- **Classical Plancherel identity on `L^ι`.** For a nontrivial additive character `ψ` of a
finite field `K`, a finite extension `L / K` and a ring homomorphism `j : R →+* ℂ`,
`∑_y |j f̂(y)|² = #L ^ #ι ∑_x |j f(x)|²`.
(sketch blueprint: `sk-cor-plancherel`, proof) -/
theorem sum_norm_sq_fourierTransformPi [Finite K] (j : R →+* ℂ) {ψ : AddChar K R} (hψ : ψ ≠ 1)
    (f : (ι → L) → R) :
    ∑ y, ‖j (fourierTransformPi ψ f y)‖ ^ 2 =
      (Fintype.card L : ℝ) ^ Fintype.card ι * ∑ x, ‖j (f x)‖ ^ 2 := by
  classical
  set g : (ι → L) → ℂ := fun x ↦ j (f x)
  set e : L → ℂ := fun t ↦ j (ψ.compTrace L t)
  have hf (y : ι → L) : j (fourierTransformPi ψ f y) = ∑ x, g x * e (∑ i, x i * y i) := by
    simp [fourierTransformPi_eq_sum_compTrace, g, e]
  have horth (x x' : ι → L) : ∑ y : ι → L, e (∑ i, (x i - x' i) * y i) =
      if x = x' then (Fintype.card L : ℂ) ^ Fintype.card ι else 0 := by
    simp only [e]
    rw [← map_sum, sum_compTrace_sum_sub_mul hψ]
    split_ifs <;> simp
  have hy (y : ι → L) : j (fourierTransformPi ψ f y) * conj (j (fourierTransformPi ψ f y)) =
      ∑ x, ∑ x', g x * conj (g x') * e (∑ i, (x i - x' i) * y i) := by
    rw [hf, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun x' _ ↦ ?_
    simp only [e]
    rw [map_mul (starRingEnd ℂ), conj_ringHom_compTrace,
      show ∑ i, (x i - x' i) * y i = ∑ i, x i * y i + -∑ i, x' i * y i by
        rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring,
      AddChar.map_add_eq_mul, map_mul j]
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
