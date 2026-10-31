/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSmoothProperFamily
public import WeilConjectures.ZetaSeries
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import WeilConjectures.ZetaLinearAlgebra.DetTrace

/-! # The condensed Lefschetz--Weil trace-to-determinant identity

Source: latest blueprint, sec-zeta-weil/sk-thm-weil-final/thm-zl-lefschetz-weil-identity.md
(blueprint: thm-zl-lefschetz-weil-identity).

The factors are the scalar extensions of the actual Q_l cohomological family; the trace
hypothesis is stated for the same mapped Q_l traces. An arbitrary chosen algebraic closure
is allowed, in its own universe.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- The point-count zeta series equals the signed product of the Frobenius determinants.
Source: latest blueprint, trace-to-determinant identity, Steps 1--5
(blueprint: thm-zl-lefschetz-weil-identity).

Proof:
1. `CondensedConstant.qlFinite` (def-weil-smooth-proper-cohomological-family) makes each
actual Q_l cohomology module finite. Let P_i be the reciprocal characteristic polynomial of
its Frobenius F_i, mapped to the chosen Qbar; its constant coefficient is one. The statement
already uses these mapped polynomials and `hTrace` the mapped Q_l traces, so no comparison
of cohomology models is needed. Qbar has characteristic zero since Q_l -> Qbar is injective.
2. lem-zl-log-det-identity, in its differentiated form `LinearMap.X_mul_derivative_charpolyRev`,
mapped along Q_l -> Qbar, gives T P_i' = -S_i P_i, where S_i has coefficient tr(F_i^n) in
degree n >= 1 and constant coefficient zero; no semisimplicity or invertibility is used.
3. Put G_i = P_i^{-1}, A_i = S_i for even i and G_i = P_i, A_i = -S_i for odd i. Since
P_i(0) = 1, T G_i' = A_i G_i in both cases, and the finite product rule gives
T (prod G_i)' = (sum A_i) (prod G_i), with constant coefficient one.
4. The constant coefficient of sum A_i is zero, and for n >= 1 its coefficient is
sum_i (-1)^i tr(F_i^n) = N_n by `hTrace`; so sum A_i is the point-count series N.
5. def-weil-point-counts-zeta gives T Z' = N Z and Z(0) = 1; map along Q -> Q_l -> Qbar.
Both the mapped zeta series and prod G_i solve T H' = N H with H(0) = 1. Since N(0) = 0 the
recursion n c_n = sum_{a+b=n} N_a c_b determines all coefficients in characteristic zero
(`PowerSeries.coeff_eq_of_X_mul_derivative_eq`), so the two series agree.
-/
theorem condensed_lefschetz_weil_identity
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (Qbar : Type v) [Field Qbar] [Algebra (Padic ell) Qbar] [IsAlgClosure (Padic ell) Qbar]
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (d : ℕ) (hSmooth : D.IsSmoothOfPureDimension X₀ d)
    (hTrace : ∀ n : ℕ, 1 ≤ n →
      (X₀.hom.pointCount n : Qbar) =
        ∑ i ∈ Finset.range (2 * d + 1), (-1 : Qbar) ^ i *
          algebraMap (Padic ell) Qbar
            (LinearMap.trace (Padic ell) (CondensedConstant.qlCohomology ell D X₀ i)
              (CondensedConstant.frobenius
                (Profinite.continuousMapRingObj (Padic ell))
                (CondensedConstant.qlScalars ell) D X₀ i ^ n))) :
    PowerSeries.map ((algebraMap (Padic ell) Qbar).comp (algebraMap ℚ (Padic ell)))
        X₀.hom.zetaSeries =
      ∏ i ∈ Finset.range (2 * d + 1),
        if Even i then
          ((CondensedConstant.qlPolynomial ell D hEll X₀ d hSmooth i).map
            (algebraMap (Padic ell) Qbar) : PowerSeries Qbar)⁻¹
        else
          ((CondensedConstant.qlPolynomial ell D hEll X₀ d hSmooth i).map
            (algebraMap (Padic ell) Qbar) : PowerSeries Qbar) := by
  classical
  have : CharZero Qbar :=
    charZero_of_injective_algebraMap (algebraMap (Padic ell) Qbar).injective
  let (i : ℤ) : Module.Finite (Padic ell) (CondensedConstant.qlCohomology ell D X₀ i) :=
    CondensedConstant.qlFinite ell D hEll X₀ d hSmooth i
  let σ := algebraMap (Padic ell) Qbar
  let τ := σ.comp (algebraMap ℚ (Padic ell))
  let F (i : ℕ) := CondensedConstant.frobenius
    (Profinite.continuousMapRingObj (Padic ell)) (CondensedConstant.qlScalars ell) D X₀ i
  let P (i : ℕ) : PowerSeries Qbar :=
    ((CondensedConstant.qlPolynomial ell D hEll X₀ d hSmooth i).map σ : PowerSeries Qbar)
  let T (i : ℕ) : PowerSeries Qbar := PowerSeries.mk fun n ↦
    if n = 0 then 0 else σ (LinearMap.trace (Padic ell)
      (CondensedConstant.qlCohomology ell D X₀ i) (F i ^ n))
  have hP (i : ℕ) : PowerSeries.X * PowerSeries.derivative Qbar (P i) = -T i * P i := by
    have h := congrArg (PowerSeries.map σ) (LinearMap.X_mul_derivative_charpolyRev (F i))
    rw [map_mul, PowerSeries.map_X, PowerSeries.map_derivative, map_mul, map_neg,
      ← Polynomial.polynomial_map_coe] at h
    change PowerSeries.X * PowerSeries.derivative Qbar
      (((F i).charpolyRev.map σ : Polynomial Qbar) : PowerSeries Qbar) = _
    rw [h]
    congr 2
    ext n
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk, T]
    split_ifs <;> simp
  have hP0 (i : ℕ) : PowerSeries.constantCoeff (P i) = 1 := by
    change PowerSeries.constantCoeff
      (((F i).charpolyRev.map σ : Polynomial Qbar) : PowerSeries Qbar) = 1
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_map,
      LinearMap.coeff_zero_charpolyRev, map_one]
  let G (i : ℕ) := if Even i then (P i)⁻¹ else P i
  let A (i : ℕ) := if Even i then T i else -T i
  have hG (i : ℕ) : PowerSeries.X * PowerSeries.derivative Qbar (G i) = A i * G i := by
    dsimp only [G, A]
    split_ifs with hi
    · simpa only [neg_neg] using
        PowerSeries.X_mul_derivative_inv (hP i) (by rw [hP0]; exact one_ne_zero)
    · exact hP i
  have hG0 (i : ℕ) : PowerSeries.constantCoeff (G i) = 1 := by
    dsimp only [G]
    split_ifs <;> simp [PowerSeries.constantCoeff_inv, hP0]
  let N : PowerSeries Qbar := PowerSeries.mk fun n ↦
    if n = 0 then 0 else (X₀.hom.pointCount n : Qbar)
  have hN : N = ∑ i ∈ Finset.range (2 * d + 1), A i := by
    ext n
    simp only [N, PowerSeries.coeff_mk, map_sum]
    by_cases hn : n = 0
    · subst n
      symm
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      dsimp only [A]
      split_ifs <;> simp [T]
    · rw [if_neg hn, hTrace n (Nat.one_le_iff_ne_zero.mpr hn)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      dsimp only [A]
      rcases Nat.even_or_odd i with hi | hi
      · simp [hi, hi.neg_one_pow, T, hn, σ, F]
      · simp [(show ¬Even i by simpa using hi), hi.neg_one_pow, T, hn, σ, F]
  have hz : PowerSeries.X * PowerSeries.derivative Qbar
      (PowerSeries.map τ X₀.hom.zetaSeries) = N * PowerSeries.map τ X₀.hom.zetaSeries := by
    have h := congrArg (PowerSeries.map τ) X₀.hom.X_mul_derivative_zetaSeries
    rw [map_mul, PowerSeries.map_X, PowerSeries.map_derivative, map_mul] at h
    rw [h]
    congr 1
    ext n
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk, N]
    split_ifs <;> simp
  have hg := PowerSeries.X_mul_derivative_prod (Finset.range (2 * d + 1))
    (fun i _ ↦ hG i)
  have hc : PowerSeries.constantCoeff (PowerSeries.map τ X₀.hom.zetaSeries) =
      PowerSeries.constantCoeff (∏ i ∈ Finset.range (2 * d + 1), G i) := by
    rw [map_prod]
    simp only [hG0, Finset.prod_const_one]
    change τ (PowerSeries.constantCoeff X₀.hom.zetaSeries) = 1
    rw [X₀.hom.constantCoeff_zetaSeries, map_one]
  have hn0 : PowerSeries.constantCoeff N = 0 := by simp [N]
  change PowerSeries.map τ X₀.hom.zetaSeries = ∏ i ∈ Finset.range (2 * d + 1), G i
  ext n
  exact PowerSeries.coeff_eq_of_X_mul_derivative_eq hz hg hc hn0
    (m := n) (fun i _ ↦ by rw [hN]) n le_rfl

end WeilConjectures
