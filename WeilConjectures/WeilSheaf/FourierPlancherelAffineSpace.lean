/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierPlancherel
public import WeilConjectures.WeilSheaf.FourierTraceAffineSpace

/-!
# The Plancherel identity on an affine space

For a nontrivial additive character `ψ` of `k₀ = 𝔽_q`, a finite index type `ι` with `r`
elements and an embedding `j : ℚ̄_ℓ ↪ ℂ`, the Fourier–Deligne transform on the affine space
`𝔸^ι` (`AlgebraicGeometry.affineSpaceFourierTransform`) multiplies the trace energy at level `n`
(`AlgebraicGeometry.WeilComplex.traceEnergy`) by `q^{nr}`:

`∑_{y ∈ 𝔽_{qⁿ}^ι} |j t_{FT_ψ(K)}(y)|² = q^{nr} ∑_{x ∈ 𝔽_{qⁿ}^ι} |j t_K(x)|²`.

It follows from the Fourier trace formula on `𝔸^ι`
(`AlgebraicGeometry.WeilComplex.traceFunction_affineSpaceFourierTransform`), the sign `(-1)^r`
having absolute value one, and the classical Plancherel identity on `𝔽_{qⁿ}^ι`
(`FiniteField.sum_norm_sq_fourierTransformPi`).

## Main statements

- `AlgebraicGeometry.WeilComplex.traceEnergy_affineSpaceFourierTransform`: the Plancherel
  identity on `𝔸^ι`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {ι : Type u} [Fintype ι] {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- **Plancherel identity on `𝔸^ι`.** For a nontrivial additive character `ψ`, every Weil
complex `K` on the affine space `𝔸^ι` with `r = #ι` and every `n ≥ 1`, the Fourier transform
multiplies the trace energy at level `n` by `q^{nr}`:

`∑_{y ∈ 𝔽_{qⁿ}^ι} |j t_{FT_ψ(K)}(y)|² = q^{nr} ∑_{x ∈ 𝔽_{qⁿ}^ι} |j t_K(x)|²`.

The nontriviality of `ψ` is needed for the orthogonality of the characters `y ↦ ψ(Tr⟨x, y⟩)`.
(blueprint: `cor-fd-plancherel`, subsection `sk-cor-plancherel`) -/
theorem WeilComplex.traceEnergy_affineSpaceFourierTransform (ψ : AddChar k₀ (PadicAlgCl l))
    (hψ : ψ ≠ 1) (j : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀)))
    {n : ℕ} (hn : 1 ≤ n) :
    ((affineSpaceFourierTransform ι ψ).obj K).traceEnergy j n =
      (Nat.card k₀ : ℝ) ^ (n * Fintype.card ι) * K.traceEnergy j n := by
  classical
  have hn' : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  let := Fintype.ofFinite (FiniteField.galoisExtension k₀ n)
  have h (L : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀))) :
      L.traceEnergy j n = ∑ x, ‖j (L.affineSpaceTraceFunction n x)‖ ^ 2 := by
    rw [traceEnergy, ← finsum_comp_equiv (AffineSpace.fieldPointsEquivPi ι k₀ _).symm,
      finsum_eq_sum_of_fintype]
    rfl
  rw [h, h]
  simp_rw [traceFunction_affineSpaceFourierTransform ψ K hn', map_mul, norm_mul, map_pow,
    map_neg, map_one, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [FiniteField.sum_norm_sq_fourierTransformPi j hψ,
    ← Nat.card_eq_fintype_card (α := FiniteField.galoisExtension k₀ n),
    FiniteField.nat_card_galoisExtension k₀ n hn', pow_mul]
  push_cast
  rfl

end AlgebraicGeometry
