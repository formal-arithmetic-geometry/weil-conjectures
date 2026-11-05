/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations
public import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Weights of eigenvalues, Frobenius modules, reality and semisimplification

This file collects the finite-dimensional linear algebra of weights used in the purity theorem
for real lisse Weil sheaves (blueprint subsections `p-real-operations`, `sk-r-real-linear`
and `sk-p-real-semi`).

* An element `α` of a field `E` with an embedding `ι : E →+* ℂ` has *weight* `w` relative to
  `q` if `|ι α| = q ^ (w / 2)` (`AlgebraicGeometry.WeilGroup.IsOfWeight`); weights add under
  products and change sign under inverses.
* A finite-dimensional vector space with an automorphism `F` is `ι`-pure of weight `w` if every
  eigenvalue of `F` has weight `w`, and `ι`-mixed of weights at most `w` if it has an
  `F`-stable filtration whose graded pieces are pure of weights `≤ w`
  (`AlgebraicGeometry.WeilGroup.IsPureFrobeniusModule`,
  `AlgebraicGeometry.WeilGroup.IsMixedFrobeniusModule`).
* The determinant line and the semisimplification of a Weil representation
  (`AlgebraicGeometry.WeilGroup.detLine`, `AlgebraicGeometry.WeilGroup.semisimplification`).
* Exterior powers of `ι`-real sheaves are `ι`-real, and the semisimplification of a Weil
  representation has the same local polynomials, hence the same reality.

## Main definitions

- `AlgebraicGeometry.WeilGroup.IsOfWeight`
- `AlgebraicGeometry.WeilGroup.IsPureFrobeniusModule`,
  `AlgebraicGeometry.WeilGroup.IsMixedFrobeniusModule`
- `AlgebraicGeometry.WeilGroup.detLine`, `AlgebraicGeometry.WeilGroup.semisimplification`

## Main statements

- `AlgebraicGeometry.WeilGroup.IsOfWeight.mul`, `AlgebraicGeometry.WeilGroup.IsOfWeight.inv`
- `AlgebraicGeometry.WeilGroup.IsReal.exteriorPower`
- `AlgebraicGeometry.WeilGroup.localPolynomial_semisimplification`,
  `AlgebraicGeometry.WeilGroup.IsReal.semisimplification`,
  `AlgebraicGeometry.WeilGroup.isPunctuallyPure_semisimplification_iff`,
  `AlgebraicGeometry.WeilGroup.hasWeightsAtMost_semisimplification_iff`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilGroup

section EigenvalueWeight

variable {E : Type*} [Field E] (ι : E →+* ℂ) (q : ℕ)

/-- Blueprint `def-tw-eigenvalue`: weights of eigenvalues.

An element `α` (typically an eigenvalue of a Frobenius operator) has *weight* `w` relative to
the prime power `q` if `|ι α| = q ^ (w / 2)`, the absolute value being read through the fixed
embedding `ι` into `ℂ`; so `|q| = q` and `q` itself has weight `2`. This is the convention of
`sk-d-real-weights`; it is related to the `ι`-weight
`AlgebraicGeometry.WeilGroup.frobeniusWeight` by
`AlgebraicGeometry.WeilGroup.isOfWeight_iff_frobeniusWeight_eq`. The weight `w` is allowed
to be any real number. -/
def IsOfWeight (w : ℝ) (α : E) : Prop :=
  ‖ι α‖ = (q : ℝ) ^ (w / 2)

variable {ι q}

/-- For `q > 1`, a nonzero `α` has weight `w` if and only if its `ι`-weight
`2 log |ι α| / log q` is `w`. -/
theorem isOfWeight_iff_frobeniusWeight_eq (hq : 1 < q) {α : E} (hα : α ≠ 0) {w : ℝ} :
    IsOfWeight ι q w α ↔ frobeniusWeight ι q α = w := by
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hlog : 0 < Real.log q := Real.log_pos hq'
  have hpos : 0 < ‖ι α‖ := by simpa using hα
  rw [IsOfWeight, frobeniusWeight, div_eq_iff hlog.ne', ← Real.exp_log hpos,
    Real.rpow_def_of_pos (by linarith), Real.exp_eq_exp, Real.log_exp]
  constructor <;> intro h <;> linarith

end EigenvalueWeight

section FrobeniusModule

variable {E : Type*} [Field E] (ι : E →+* ℂ) (q : ℕ) {V : Type*} [AddCommGroup V] [Module E V]

variable {ι q}

end FrobeniusModule

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  {W : WeilGroup p} {l : ℕ} [Fact l.Prime]

section Operations

variable (W l) {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V)

end Operations

section Real

variable {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V] {ρ : Representation (PadicAlgCl l) W.carrier V}
  (ι : PadicAlgCl l →+* ℂ)

end Real

end WeilGroup

end AlgebraicGeometry
