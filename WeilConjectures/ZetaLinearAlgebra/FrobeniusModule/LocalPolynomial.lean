/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TraceSeries

/-!
# The local polynomial determines the traces of the powers of the Frobenius

The determinant-trace identity `T (det (1 - T F))' = -(∑_{n ≥ 1} tr (Fⁿ) Tⁿ) det (1 - T F)`
(`LinearMap.X_mul_derivative_charpolyRev`) recovers the traces `tr (Fⁿ)`, `n ≥ 1`, from the
local polynomial `det (1 - T F)`, which has constant coefficient `1`; its degree is the dimension,
the trace of `F⁰`. Hence two Frobenius modules whose local polynomials have the same images under
ring homomorphisms `φ` and `ψ` into a field have traces of the powers of the Frobenius with the
same images under `φ` and `ψ`.

## Main results

- `LinearMap.map_trace_pow_eq_of_map_charpolyRev_eq`: the statement for endomorphisms, for
  powers `n ≥ 1`.
- `FrobeniusModule.map_trace_frobeniusEnd_pow_eq_of_map_localPolynomial_eq`: the statement for
  Frobenius modules, for all powers.
-/

@[expose] public section

open PowerSeries

namespace LinearMap

variable {K L V : Type*} [Field K] [Field L] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The image under `φ` of the generating series `∑_{n ≥ 1} tr (fⁿ) Xⁿ` of the traces of the
powers of `f` is `-X P'/P` for the image `P` of `det (1 - X f)`. -/
theorem map_mk_trace_pow (f : Module.End K V) (φ : K →+* L) :
    PowerSeries.map φ (PowerSeries.mk fun n ↦ if n = 0 then 0 else LinearMap.trace K V (f ^ n)) =
      -(X * derivative L ((f.charpolyRev.map φ : Polynomial L) : L⟦X⟧)) *
        ((f.charpolyRev.map φ : Polynomial L) : L⟦X⟧)⁻¹ := by
  set P : L⟦X⟧ := ((f.charpolyRev.map φ : Polynomial L) : L⟦X⟧)
  have hP : constantCoeff P = 1 := by
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_map, LinearMap.coeff_zero_charpolyRev,
      map_one]
  have h := congrArg (PowerSeries.map φ) (X_mul_derivative_charpolyRev f)
  rw [map_mul, map_mul, map_X, map_derivative, map_neg, ← Polynomial.polynomial_map_coe] at h
  change X * derivative L P = _ * P at h
  change _ = -(X * derivative L P) * P⁻¹
  have hPP : P * P⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hP]; exact one_ne_zero)
  rw [h]
  linear_combination (-PowerSeries.map φ (PowerSeries.mk fun n ↦
    if n = 0 then 0 else LinearMap.trace K V (f ^ n))) * hPP

/-- If the images of the local polynomials `det (1 - X g)` and `det (1 - X f)` under `φ` and `ψ`
agree, then so do the images of the traces of the `n`-th powers, `n ≥ 1`. -/
theorem map_trace_pow_eq_of_map_charpolyRev_eq {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (f : Module.End K V) (g : Module.End K W) (φ ψ : K →+* L)
    (h : g.charpolyRev.map φ = f.charpolyRev.map ψ) {n : ℕ} (hn : n ≠ 0) :
    φ (LinearMap.trace K W (g ^ n)) = ψ (LinearMap.trace K V (f ^ n)) := by
  have h' := congrArg (coeff n) ((map_mk_trace_pow g φ).trans
    ((congrArg (fun P : Polynomial L ↦ -(X * derivative L (P : L⟦X⟧)) * (P : L⟦X⟧)⁻¹) h).trans
      (map_mk_trace_pow f ψ).symm))
  simpa [hn] using h'

end LinearMap

namespace FrobeniusModule

universe u v t

variable {K L : Type*} [Field K] [Field L]

/-- Two Frobenius modules whose local polynomials `det (1 - T F)` have the same images under
`φ` and `ψ` have traces of the powers of the Frobenius with the same images under `φ` and `ψ`:
for `n ≥ 1` by the determinant-trace identity, and for `n = 0` because the degree of the local
polynomial is the dimension. -/
theorem map_trace_frobeniusEnd_pow_eq_of_map_localPolynomial_eq (M : FrobeniusModule.{u} K)
    (N : FrobeniusModule.{t} K) (φ ψ : K →+* L)
    (h : N.localPolynomial.map φ = M.localPolynomial.map ψ) (n : ℕ) :
    φ (LinearMap.trace K _ (N.frobeniusEnd ^ n)) =
      ψ (LinearMap.trace K _ (M.frobeniusEnd ^ n)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have hd := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_map, Polynomial.natDegree_map, natDegree_localPolynomial,
      natDegree_localPolynomial] at hd
    simp [LinearMap.trace_one, hd]
  · exact LinearMap.map_trace_pow_eq_of_map_charpolyRev_eq _ _ φ ψ h hn

end FrobeniusModule
