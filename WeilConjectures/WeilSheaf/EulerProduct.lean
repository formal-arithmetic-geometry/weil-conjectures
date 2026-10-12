/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.LSeries
public import WeilConjectures.WeilSheaf.StalkTensorTrace

/-!
# The `L`-series of a lisse Weil sheaf on an affine curve

On a smooth geometrically connected affine curve `U₀`, the Grothendieck–Lefschetz trace formula
writes the `L`-series of a lisse Weil sheaf `G` as the ratio
`det(1 - Ft | H_c¹(U, G)) / det(1 - Ft | H_c²(U, G))` of the determinants of the Frobenius on
compactly supported cohomology. For an `ι`-real `G` the local factors of the `L`-series of the
tensor square `G ⊗ G` have nonnegative coefficients.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsReal.hasNonnegCoeffs_lFactor_tensorObj`: the local factors of
  `L(U₀, G ⊗ G, t)` have nonnegative coefficients.
- `AlgebraicGeometry.WeilSheaf.lSeries_mul_localPolynomial_compactlySupportedCohomology_two`: the
  Euler product of the `L`-series, stated with `sorry`; it is the curve case of the
  Grothendieck–Lefschetz trace formula.
-/

@[expose] public section

universe u

open CategoryTheory PowerSeries

open scoped ComplexOrder

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Positivity

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- For an `ι`-real Weil sheaf the images under `ι` of the traces of the powers of the local
Frobenius are real: the local polynomial has real coefficients. -/
theorem IsReal.conj_map_trace_frobeniusEnd_pow {ι : PadicAlgCl l →+* ℂ} {G : WeilSheaf k₀ l X}
    (hreal : G.IsReal ι) (x : X.finitePoints) (k : ℕ) :
    (starRingEnd ℂ) (ι (LinearMap.trace (PadicAlgCl l) _ ((G.stalk x).frobeniusEnd ^ k))) =
      ι (LinearMap.trace (PadicAlgCl l) _ ((G.stalk x).frobeniusEnd ^ k)) := by
  refine (FrobeniusModule.map_trace_frobeniusEnd_pow_eq_of_map_localPolynomial_eq (G.stalk x)
    (G.stalk x) ι ((starRingEnd ℂ).comp ι) ?_ k).symm
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_map, RingHom.comp_apply, hreal x n]

/-- **Even tensor powers of a real sheaf are positive**, for tensor squares: if `G` is lisse and
`ι`-real, then every local factor `ι det(1 - Fₓ t^{d(x)} | (G ⊗ G)_x̄)⁻¹` of the `L`-series of
`G ⊗ G` has nonnegative real coefficients (and constant coefficient `1`,
`AlgebraicGeometry.WeilSheaf.constantCoeff_lFactor`). The traces of the powers of the local
Frobenius of `G ⊗ G` are the squares `(ι tr(Gₓᵏ))²` of real numbers, and the logarithmic
derivative of the local factor is their generating series.
(blueprint: `lem-rp-even-tensor-positivity`, the case of tensor squares) -/
theorem IsReal.hasNonnegCoeffs_lFactor_tensorObj {ι : PadicAlgCl l →+* ℂ}
    {G : WeilSheaf k₀ l X} (hG : G.IsLisse) (hreal : G.IsReal ι) (x : X.finitePoints) :
    ((G.tensorObj G hG).lFactor ι x).HasNonnegCoeffs := by
  rw [hasNonnegCoeffs_iff]
  refine coeff_nonneg_of_X_mul_derivative_eq (X_mul_derivative_lFactor ι _ x) (fun n ↦ ?_)
    (by simp [coeff_lFactorLogDeriv]) (by simp [constantCoeff_lFactor])
  rw [coeff_lFactorLogDeriv]
  split_ifs
  · rw [trace_stalk_tensorObj_frobeniusEnd_pow, map_mul]
    set z := ι (LinearMap.trace (PadicAlgCl l) _ ((G.stalk x).frobeniusEnd ^
      (n / (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1)))
    have hz : z = (z.re : ℂ) := (Complex.conj_eq_iff_re.1 (hreal.conj_map_trace_frobeniusEnd_pow
      x _)).symm
    rw [hz, ← Complex.ofReal_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    exact Complex.zero_le_real.2 (mul_nonneg (Nat.cast_nonneg _) (mul_self_nonneg _))
  · exact le_rfl

end Positivity

section EulerProduct

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [IsAffine U]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))]

/-- **Euler product of the `L`-function of a lisse sheaf.** Let `U₀` be a smooth geometrically
connected affine curve and `G` a lisse Weil sheaf on `U₀`. Then, as power series in `t`,

`∏_{x ∈ |U₀|} ι det(1 - Fₓ t^{d(x)} | G_x̄)⁻¹ =
  ι det(1 - F t | H_c¹(U, G)) / ι det(1 - F t | H_c²(U, G))`,

stated as `L(U₀, G, t) · ι det(1 - F t | H_c²(U, G)) = ι det(1 - F t | H_c¹(U, G))`. This is the
graded form of the Grothendieck–Lefschetz trace formula on the curve, `H_c⁰(U, G)` vanishing
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero`).
(blueprint: `cor-rp-euler-product`) -/
theorem lSeries_mul_localPolynomial_compactlySupportedCohomology_two (ι : PadicAlgCl l →+* ℂ)
    (G : WeilSheaf k₀ l U) (hG : G.IsLisse) :
    G.lSeries ι *
        (((G.compactlySupportedCohomology 2).localPolynomial.map ι : Polynomial ℂ) : ℂ⟦X⟧) =
      (((G.compactlySupportedCohomology 1).localPolynomial.map ι : Polynomial ℂ) : ℂ⟦X⟧) := by
  sorry

end EulerProduct

end WeilSheaf

end AlgebraicGeometry
