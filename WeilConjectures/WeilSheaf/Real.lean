/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Polynomial.FieldDivision
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.WeilSheaf.Stalk

/-!
# Real Weil sheaves and their eigenvalues

A Weil sheaf `G` is `ι`-real (`AlgebraicGeometry.WeilSheaf.IsReal`) if at every closed point `x`
the polynomial `ι det(1 - T Frobₓ | G_x̄)` has real coefficients. This file proves the equivalent
form in terms of eigenvalues: the multiset of complex eigenvalues of the local Frobenius at every
closed point is stable under complex conjugation. The linear-algebra statement is
`FrobeniusModule.isReal_iff_map_conj_roots_charpoly`.

## Main statements

* `FrobeniusModule.isReal_iff_map_conj_roots_charpoly`: over an algebraically closed field, a
  Frobenius module is `ι`-real if and only if the multiset of complex eigenvalues of its Frobenius
  is stable under complex conjugation.
* `AlgebraicGeometry.WeilSheaf.isReal_iff_map_conj_roots_charpoly`: the same for the local
  Frobenius of a Weil sheaf at every closed point.

## Blueprint

`AlgebraicGeometry.WeilSheaf.IsReal` together with
`AlgebraicGeometry.WeilSheaf.isReal_iff_map_conj_roots_charpoly` implements
`definition-real-sheaves--1` for Weil sheaves; with
`AlgebraicGeometry.WeilSheaf.IsReal.conj_map_trace_frobeniusEnd_pow`
(`definition-real-sheaves--2`) they implement `definition-real-sheaves`.
-/

@[expose] public section

universe u v

open Polynomial

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- Over an algebraically closed field `K`, a Frobenius module `M` is `ι`-real, i.e. the image
under `ι` of its local polynomial `det(1 - T F)` has real coefficients, if and only if the
multiset of complex eigenvalues `ι α` of its Frobenius `F` is stable under complex conjugation.
(blueprint: `definition-real-sheaves--1`) -/
theorem isReal_iff_map_conj_roots_charpoly [IsAlgClosed K] (ι : K →+* ℂ)
    (M : FrobeniusModule.{u, v} K) :
    M.IsReal ι ↔ ((M.frobeniusEnd.charpoly.roots.map ι).map (starRingEnd ℂ)) =
      M.frobeniusEnd.charpoly.roots.map ι := by
  set R := M.frobeniusEnd.charpoly.roots
  have hR : (0 : K) ∉ R :=
    LinearMap.zero_notMem_roots_charpoly (LinearEquiv.isUnit_det' M.frobenius)
  have hM : (0 : ℂ) ∉ R.map ι := by
    simp only [Multiset.mem_map, map_eq_zero, not_exists, not_and]
    rintro α hα rfl
    exact hR hα
  have hM' : (0 : ℂ) ∉ (R.map ι).map (starRingEnd ℂ) := by simpa using hM
  have hP : M.localPolynomial.map ι = ((R.map ι).map fun β ↦ 1 - C β * X).prod := by
    rw [localPolynomial, LinearMap.charpolyRev_eq_prod_roots,
      map_multiset_prod_one_sub_C_mul_X]
  have key : M.IsReal ι ↔
      (M.localPolynomial.map ι).map (starRingEnd ℂ) = M.localPolynomial.map ι := by
    refine ⟨fun h ↦ ?_, fun h n ↦ ?_⟩
    · ext n
      simpa [coeff_map] using h n
    · simpa [coeff_map] using congrArg (coeff · n) h
  rw [key, hP, map_multiset_prod_one_sub_C_mul_X]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  have := congrArg roots h
  rw [roots_multiset_prod_one_sub_C_mul_X hM', roots_multiset_prod_one_sub_C_mul_X hM] at this
  exact Multiset.map_injective inv_injective this

end FrobeniusModule

namespace AlgebraicGeometry.WeilSheaf

variable {l : ℕ} [Fact l.Prime]
variable {k₀ : Type u} [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- A Weil sheaf `G` is `ι`-real, i.e. `ι det(1 - T Frobₓ | G_x̄)` has real coefficients at every
closed point `x`, if and only if at every closed point the multiset of complex eigenvalues of the
local Frobenius `Frobₓ` on `G_x̄` is stable under complex conjugation.
(blueprint: `definition-real-sheaves`, `definition-real-sheaves--1`) -/
theorem isReal_iff_map_conj_roots_charpoly (ι : PadicAlgCl l →+* ℂ) (G : WeilSheaf k₀ l X) :
    G.IsReal ι ↔ ∀ x : X.finitePoints,
      ((G.stalk x).frobeniusEnd.charpoly.roots.map ι).map (starRingEnd ℂ) =
        (G.stalk x).frobeniusEnd.charpoly.roots.map ι :=
  forall_congr' fun x ↦ (G.stalk x).isReal_iff_map_conj_roots_charpoly ι

end AlgebraicGeometry.WeilSheaf
