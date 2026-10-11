/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.FieldPoints
public import WeilConjectures.FourierTransform.Classical
public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.Stalk
public import WeilConjectures.ZetaSeries

/-!
# The trace function of the Fourier–Deligne transform

Let `k₀` be a finite field with `q` elements and `ψ` an additive character of `k₀` with values
in `ℚ̄_ℓ`. The `𝔽_{qⁿ}`-rational points of the affine line are the elements of `𝔽_{qⁿ}`
(`AlgebraicGeometry.AffineSpace.fieldPointsEquiv`), so the trace function `t_K` of a Weil
complex `K` on `𝔸¹` at level `n` is a function on `𝔽_{qⁿ}`. The *Fourier trace formula* says
that the trace function of the Fourier–Deligne transform `FT_ψ(K)` is, up to the sign coming
from the shift `[1]`, the classical Fourier transform of the trace function of `K`
(`FiniteField.fourierTransform`):

`t_{FT_ψ(K)}(y) = -∑_{x ∈ 𝔽_{qⁿ}} t_K(x) ψ(Tr_{𝔽_{qⁿ}/k₀}(x y))`.

The two numerical identities of the transform follow from the corresponding identities of the
classical transform: *Plancherel*,
`∑_y |ι t_{FT_ψ(K)}(y)|² = qⁿ ∑_x |ι t_K(x)|²`, and *trace-level inversion*,
`t_{FT_{ψ⁻¹} FT_ψ(K)}(y) = qⁿ t_K(y)`.

## Main statements

- `AlgebraicGeometry.WeilComplex.traceFunction_fourierTransform`: the Fourier trace formula.
- `AlgebraicGeometry.WeilComplex.sum_norm_sq_traceFunction_fourierTransform`: Plancherel.
- `AlgebraicGeometry.WeilComplex.traceFunction_fourierTransform_inv_fourierTransform`:
  trace-level Fourier inversion.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The trace function of a Weil complex on the affine line at level `n`, as a function on
`𝔽_{qⁿ}`, through the identification `𝔸¹(𝔽_{qⁿ}) ≃ 𝔽_{qⁿ}`. -/
noncomputable def affineLineTraceFunction (K : WeilComplex k₀ l (affineLine k₀)) (n : ℕ)
    (x : FiniteField.galoisExtension k₀ n) : PadicAlgCl l :=
  K.traceFunction n ((AffineSpace.fieldPointsEquiv k₀ _).symm x)

/-- **The Fourier trace formula.** For an additive character `ψ` of `k₀`, a Weil complex `K` on
the affine line, `n ≥ 1` and `y ∈ 𝔽_{qⁿ}`,

`t_{FT_ψ(K)}(y) = -∑_{x ∈ 𝔽_{qⁿ}} t_K(x) ψ(Tr_{𝔽_{qⁿ}/k₀}(x y))`:

up to the sign coming from the shift `[1]`, the trace function of the transform is the
classical Fourier transform of the trace function of `K`.
(sketch blueprint: `sk-thm-fourier-trace-formula`; blueprint: `thm-fd-fourier-trace`) -/
theorem traceFunction_fourierTransform (ψ : AddChar k₀ (PadicAlgCl l))
    (K : WeilComplex k₀ l (affineLine k₀)) {n : ℕ} (hn : n ≠ 0)
    [Fintype (FiniteField.galoisExtension k₀ n)] (y : FiniteField.galoisExtension k₀ n) :
    ((fourierTransform ψ).obj K).affineLineTraceFunction n y =
      -FiniteField.fourierTransform ψ (K.affineLineTraceFunction n) y :=
  sorry

/-- The `qⁿ` elements of `𝔽_{qⁿ}`, as a scalar. -/
private lemma card_galoisExtension_eq {n : ℕ} (hn : n ≠ 0)
    [Fintype (FiniteField.galoisExtension k₀ n)] :
    (Fintype.card (FiniteField.galoisExtension k₀ n) : ℕ) = Nat.card k₀ ^ n := by
  rw [← Nat.card_eq_fintype_card, FiniteField.nat_card_galoisExtension k₀ n hn]

/-- **Plancherel.** For a nontrivial additive character `ψ` of `k₀`, a field embedding
`ι : ℚ̄_ℓ ⟶ ℂ`, a Weil complex `K` on the affine line and `n ≥ 1`,

`∑_{y ∈ 𝔽_{qⁿ}} |ι t_{FT_ψ(K)}(y)|² = qⁿ ∑_{x ∈ 𝔽_{qⁿ}} |ι t_K(x)|²`.

It is the classical Plancherel identity (`FiniteField.sum_norm_sq_fourierTransform`) for the
Fourier sum of the trace formula; no weight enters.
(sketch blueprint: `sk-cor-plancherel`; blueprint: `cor-fd-plancherel`) -/
theorem sum_norm_sq_traceFunction_fourierTransform (ι : PadicAlgCl l →+* ℂ)
    {ψ : AddChar k₀ (PadicAlgCl l)} (hψ : ψ ≠ 1) (K : WeilComplex k₀ l (affineLine k₀))
    {n : ℕ} (hn : n ≠ 0) [Fintype (FiniteField.galoisExtension k₀ n)] :
    ∑ y, ‖ι (((fourierTransform ψ).obj K).affineLineTraceFunction n y)‖ ^ 2 =
      (Nat.card k₀ : ℝ) ^ n * ∑ x, ‖ι (K.affineLineTraceFunction n x)‖ ^ 2 := by
  simp_rw [traceFunction_fourierTransform ψ K hn, map_neg, norm_neg]
  rw [FiniteField.sum_norm_sq_fourierTransform ι hψ, card_galoisExtension_eq hn]
  push_cast
  rfl

/-- **Trace-level Fourier inversion.** For a nontrivial additive character `ψ` of `k₀`, a Weil
complex `K` on the affine line, `n ≥ 1` and `y ∈ 𝔽_{qⁿ}`,

`t_{FT_{ψ⁻¹} FT_ψ(K)}(y) = qⁿ t_K(y)`,

which is the trace function of the Tate twist `K(-1)` at points of degree `n`. It is the
Fourier trace formula applied twice, followed by classical Fourier inversion
(`FiniteField.fourierTransform_inv_fourierTransform`).
(sketch blueprint: `sk-prop-double-trace`) -/
theorem traceFunction_fourierTransform_inv_fourierTransform {ψ : AddChar k₀ (PadicAlgCl l)}
    (hψ : ψ ≠ 1) (K : WeilComplex k₀ l (affineLine k₀)) {n : ℕ} (hn : n ≠ 0)
    (y : FiniteField.galoisExtension k₀ n) :
    ((fourierTransform ψ⁻¹).obj ((fourierTransform ψ).obj K)).affineLineTraceFunction n y =
      (Nat.card k₀ : PadicAlgCl l) ^ n * K.affineLineTraceFunction n y := by
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  let := Fintype.ofFinite (FiniteField.galoisExtension k₀ n)
  have h : ((fourierTransform ψ).obj K).affineLineTraceFunction n =
      fun x ↦ -FiniteField.fourierTransform ψ (K.affineLineTraceFunction n) x :=
    funext fun x ↦ traceFunction_fourierTransform ψ K hn x
  rw [traceFunction_fourierTransform ψ⁻¹ _ hn, h, FiniteField.fourierTransform_neg, neg_neg,
    FiniteField.fourierTransform_inv_fourierTransform hψ, card_galoisExtension_eq hn]
  push_cast
  rfl

end AlgebraicGeometry.WeilComplex
