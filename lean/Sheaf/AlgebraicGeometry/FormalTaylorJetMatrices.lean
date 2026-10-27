module

public import Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum
public import Sheaf.LinearAlgebra.Matrix.MinorIdeal
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Formal Taylor jet matrices and origin-rank minors

Source: Bierstone--Milman, Invent. Math. 128 (1997), Definition 7.9,
(7.12) and Definition 7.13, pp.265--266.
(blueprint: def-trf-formal-taylor-jet-matrices)

The finite monomial indices, factorials, unrestricted Taylor matrix, its origin
rank and the next-sized minor ideal are definitions. No presentation, pivot or
Hilbert-stratum theorem is imported to construct them.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace AlgebraicGeometry.HilbertCoefficient

open Classical in
/-- The finite monomial index set of total degree at most `t`, including the constant monomial.

Source: Bierstone--Milman, Invent. Math. 128 (1997), Definitions 7.9, 7.12--7.13,
Theorem 7.14 and Remarks 9.1, 9.5 (blueprint: def-trf-formal-taylor-jet-matrices). -/
def jetExponents (σ : Type v) [Fintype σ] (t : ℕ) : Finset (σ →₀ ℕ) :=
  (Finsupp.finite_of_degree_le (σ := σ) t).toFinset

open Classical in
/-- Multi-index factorial, mapped to the coefficient ring.

Source: Bierstone--Milman, Invent. Math. 128 (1997), Definitions 7.9, 7.12--7.13,
Theorem 7.14 and Remarks 9.1, 9.5 (blueprint: def-trf-formal-taylor-jet-matrices). -/
def multiFactorial {σ : Type v} [Fintype σ] (R : Type u) [CommRing R]
    (δ : σ →₀ ℕ) : R :=
  ∏ j : σ, (Nat.factorial (δ j) : R)

open Classical in
/-- Reindex a finite matrix by `Fin` to use the recorded `Matrix.minorIdeal` definition.

Source: Bierstone--Milman, Invent. Math. 128 (1997), Definitions 7.9, 7.12--7.13,
Theorem 7.14 and Remarks 9.1, 9.5 (blueprint: def-trf-formal-taylor-jet-matrices). -/
def finiteMinorIdeal {R : Type u} [CommRing R] {ι κ : Type v}
    [Fintype ι] [Fintype κ] (B : Matrix ι κ R) (r : ℕ) : Ideal R :=
  Matrix.minorIdeal (Fintype.card ι) (Fintype.card κ) r
    (B.submatrix (Fintype.equivFin ι).symm (Fintype.equivFin κ).symm)

open Classical in
/-- The matrix with columns `Y^η fᵢ(X+Y)` modulo terms of degree greater than `t`.

Source: Bierstone--Milman, Invent. Math. 128 (1997), Definitions 7.9, 7.12--7.13,
Theorem 7.14 and Remarks 9.1, 9.5 (blueprint: def-trf-formal-taylor-jet-matrices). -/
def formalJetMatrix {σ : Type v} [Fintype σ] {L : Type u} [Field L]
    {s : ℕ} (f : Fin s → MvPowerSeries σ L) (t : ℕ) :
    Matrix ↥(jetExponents σ t) (Fin s × ↥(jetExponents σ t)) (MvPowerSeries σ L) :=
  fun δ iη ↦ if iη.2.val ≤ δ.val then
    MvPowerSeries.C ((multiFactorial L (δ.val - iη.2.val))⁻¹) *
      iteratedPartial (δ.val - iη.2.val) (f iη.1)
  else 0

open Classical in
/-- The rank at the formal origin, with no subtraction or negative-rank convention.

Source: Bierstone--Milman, Invent. Math. 128 (1997), Definitions 7.9, 7.12--7.13,
Theorem 7.14 and Remarks 9.1, 9.5 (blueprint: def-trf-formal-taylor-jet-matrices). -/
def formalJetRank {σ : Type v} [Fintype σ] {L : Type u} [Field L]
    {s : ℕ} (f : Fin s → MvPowerSeries σ L) (t : ℕ) : ℕ :=
  Matrix.rank (fun δ iη ↦ MvPowerSeries.constantCoeff (formalJetMatrix f t δ iη))

open Classical in
/-- The ideal `Jₜ` of minors one size above the rank at the formal origin.

Source: Bierstone--Milman, Invent. Math. 128 (1997), Definitions 7.9, 7.12--7.13,
Theorem 7.14 and Remarks 9.1, 9.5 (blueprint: def-trf-formal-taylor-jet-matrices). -/
def formalJetMinorIdeal {σ : Type v} [Fintype σ] {L : Type u} [Field L]
    {s : ℕ} (f : Fin s → MvPowerSeries σ L) (t : ℕ) : Ideal (MvPowerSeries σ L) :=
  finiteMinorIdeal (formalJetMatrix f t) (formalJetRank f t + 1)

end AlgebraicGeometry.HilbertCoefficient
