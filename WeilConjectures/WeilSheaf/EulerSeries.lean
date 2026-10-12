/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.PiTopology
public import WeilConjectures.PointCount
public import WeilConjectures.WeilSheaf.Cohomology

/-!
# The Euler series of a Weil sheaf

Let `F` be a Weil sheaf on a scheme `X` of finite type over `k₀ = 𝔽_q`, and `ι : ℚ̄_ℓ →+* ℂ`. Its
cohomology `Hⁱ(X ⊗ k̄, F)` and compactly supported cohomology `H_cⁱ(X ⊗ k̄, F)` with their
geometric Frobenius are `AlgebraicGeometry.WeilSheaf.cohomology` and
`AlgebraicGeometry.WeilSheaf.compactlySupportedCohomology`. Its *Euler series* is the locally
finite product over the closed points `x` of `X`

`L_ι(X₀, F, T) = ∏_{x ∈ |X₀|} ι P_x(F, T ^ e_x)⁻¹ ∈ 1 + T ℂ⟦T⟧`,

where `P_x(F, T) = det (1 - T F_x ∣ F_x̄)` is the local polynomial of the stalk at `x` and
`e_x` the degree of `x`. Locally finite means that only finitely many factors contribute to a
fixed coefficient: there are finitely many closed points of bounded degree.

This is the sheaf-level form of `AlgebraicGeometry.WeilGroup.eulerSeries` (which treats lisse
sheaves through their Weil representations); it applies to every constructible Weil sheaf, for
instance the extension by zero or the direct image of a lisse sheaf on an open.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.eulerFactor`: the local factor `ι P_x(F, T ^ e_x)⁻¹`.
- `AlgebraicGeometry.WeilSheaf.eulerSeries`: the Euler series `L_ι(X₀, F, T)`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.multipliable_eulerFactor`: the product converges.
- `AlgebraicGeometry.WeilSheaf.constantCoeff_eulerSeries`: it lies in `1 + T ℂ⟦T⟧`.
-/

@[expose] public section

universe u

open scoped PowerSeries.WithPiTopology

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X)
  (ι : PadicAlgCl l →+* ℂ)

/-- The local factor `ι P_x(F, T ^ e_x)⁻¹` of the Euler series of a Weil sheaf `F` at a closed
point `x` of degree `e_x`, where `P_x(F, T) = det (1 - T F_x)` is the local polynomial of the
stalk of `F` at `x`. -/
noncomputable def eulerFactor (x : X.finitePoints) : PowerSeries ℂ :=
  ((((F.stalk x).localPolynomial.map ι).comp
    (Polynomial.X ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) : Polynomial ℂ) :
      PowerSeries ℂ)⁻¹

/-- The complex local polynomial of a stalk takes the value `1` at `0`. -/
theorem eval_zero_map_localPolynomial_stalk (x : X.finitePoints) :
    ((F.stalk x).localPolynomial.map ι).eval 0 = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
    FrobeniusModule.localPolynomial, LinearMap.coeff_zero_charpolyRev, map_one]

/-- The constant term of a local factor of the Euler series is `1`. -/
theorem constantCoeff_eulerFactor (x : X.finitePoints) :
    PowerSeries.constantCoeff (F.eulerFactor ι x) = 1 := by
  rw [eulerFactor, PowerSeries.constantCoeff_inv, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp,
    Polynomial.eval_pow, Polynomial.eval_X,
    zero_pow ((X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2),
    eval_zero_map_localPolynomial_stalk, inv_one]

/-- Blueprint `d-real-cohom`, `sk-d-real-cohom`: the Euler product of a Weil sheaf converges in
the product topology of `ℂ⟦T⟧`. The local factor at `x` is `1` modulo `T ^ e_x`, and a scheme of
finite type over `k₀` has only finitely many closed points of bounded degree
(`AlgebraicGeometry.Scheme.Hom.finite_setOf_degreeOver_le`), so only finitely many factors
contribute to a fixed coefficient. -/
theorem multipliable_eulerFactor [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    Multipliable (F.eulerFactor ι) := by
  set p := X ↘ Spec (CommRingCat.of k₀)
  refine PowerSeries.WithPiTopology.multipliable_inv_of_X_pow_dvd_sub_one
    (e := fun x : X.finitePoints ↦ p.degreeOver x.1) (fun x ↦ p.degreeOver_ne_zero x.2)
    (fun x ↦ ?_) p.finite_setOf_degreeOver_le
  set P := (F.stalk x).localPolynomial.map ι
  obtain ⟨Q, hQ⟩ := Polynomial.X_dvd_iff.2 (show (P - 1).coeff 0 = 0 by
    rw [Polynomial.coeff_sub, Polynomial.coeff_one_zero, Polynomial.coeff_zero_eq_eval_zero,
      eval_zero_map_localPolynomial_stalk, sub_self])
  have h : P.comp (Polynomial.X ^ p.degreeOver x.1) - 1 =
      Polynomial.X ^ p.degreeOver x.1 * Q.comp (Polynomial.X ^ p.degreeOver x.1) := by
    rw [← Polynomial.one_comp (p := Polynomial.X ^ p.degreeOver x.1), ← Polynomial.sub_comp, hQ,
      Polynomial.mul_comp, Polynomial.X_comp]
  refine ⟨(Q.comp (Polynomial.X ^ p.degreeOver x.1) : PowerSeries ℂ), ?_⟩
  have h' := congrArg (fun q : Polynomial ℂ ↦ (q : PowerSeries ℂ)) h
  simpa only [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_X] using h'

/-- Blueprint `d-real-cohom`, `sk-d-real-cohom`: Cohomology and the Euler series.

The Euler series `L_ι(X₀, F, T) = ∏_{x ∈ |X₀|} ι P_x(F, T ^ e_x)⁻¹` of a Weil sheaf `F`, the
product over the closed points `x` of the inverses of the local polynomials
`P_x(F, T) = det (1 - T F_x ∣ F_x̄)` of the stalks, transported to `ℂ` along `ι` and evaluated
at `T ^ e_x`. It is taken in the product topology on `ℂ⟦T⟧`, in which it converges when `X` is
of finite type over `k₀` (`AlgebraicGeometry.WeilSheaf.multipliable_eulerFactor`), and then lies
in `1 + T ℂ⟦T⟧` (`AlgebraicGeometry.WeilSheaf.constantCoeff_eulerSeries`). The cohomology
groups `Hⁱ(X ⊗ k̄, F)` and `H_cⁱ(X ⊗ k̄, F)` with their geometric Frobenius, the other half of
the blueprint definition, are `AlgebraicGeometry.WeilSheaf.cohomology` and
`AlgebraicGeometry.WeilSheaf.compactlySupportedCohomology`. -/
noncomputable def eulerSeries : PowerSeries ℂ :=
  ∏' x : X.finitePoints, F.eulerFactor ι x

/-- Blueprint `d-real-cohom`, `sk-d-real-cohom`: the Euler series of a Weil sheaf on a scheme of
finite type over `k₀` lies in `1 + T ℂ⟦T⟧`, every local factor having constant term `1`. -/
theorem constantCoeff_eulerSeries [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    PowerSeries.constantCoeff (F.eulerSeries ι) = 1 := by
  have h := (F.multipliable_eulerFactor ι).hasProd.map (PowerSeries.constantCoeff (R := ℂ))
    (PowerSeries.WithPiTopology.continuous_constantCoeff ℂ)
  simp only [Function.comp_def, constantCoeff_eulerFactor] at h
  exact h.unique hasProd_one

end AlgebraicGeometry.WeilSheaf
