/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import WeilConjectures.ZetaFunction

@[expose] public section

/-!
# Local weights, reality and determinant weights

Let `ρ` be a lisse Weil representation on a curve `C₀ / 𝔽_q` and `ι : ℚ̄_ℓ →+* ℂ` a field
embedding. At a closed point `x` of `C₀` the local Frobenius `F_x` acts on the geometric
stalk, and the local polynomial is `P_x(ρ, T) = det (1 - T F_x)`. The `ι`-weight of a nonzero
local eigenvalue `α` is `2 log |ι α| / log q_x`.

This file defines these notions, punctual `ι`-purity, the bound `weights ≤ w`, `ι`-reality,
and the determinant weight `dw_ι(V) = wt_ι(det V) / rank V` together with the rank and
weight sums above a given determinant weight.

## Main definitions

- `AlgebraicGeometry.weight` : the `ι`-weight `2 log |ι α| / log q_x` of an eigenvalue.
- `AlgebraicGeometry.WeilGroup.localPolynomial` : `P_x(ρ, T) = det (1 - T F_x)`.
- `AlgebraicGeometry.WeilGroup.IsPunctuallyPure`, `HasWeightsAtMost`, `IsReal`.
- `AlgebraicGeometry.WeilGroup.HasDetWeight` : `dw_ι(ρ) = γ`.
- `AlgebraicGeometry.rankAbove`, `AlgebraicGeometry.weightSumAbove` : `N_γ` and `B_γ`.

## Main statements

- `AlgebraicGeometry.WeilGroup.localPolynomial_eq_charpolyRev_of_isConj` : the local
  polynomial only depends on the Frobenius conjugacy class.
-/

universe u

open CategoryTheory Polynomial

namespace AlgebraicGeometry

/-- Blueprint `sk-d-real-weights`: Local weights and reality.

The `ι`-weight of a nonzero local eigenvalue `α`, relative to the residue cardinality `qₓ`:
`wt_{ι, qₓ}(α) = 2 log |ι α| / log qₓ`. -/
noncomputable def weight {E : Type*} [Field E] (ι : E →+* ℂ) (qx : ℕ) (α : E) : ℝ :=
  2 * Real.log ‖ι α‖ / Real.log qx

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)}

namespace WeilGroup

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type*} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V)

/-- Blueprint `sk-d-real-weights`: Local weights and reality.

The local polynomial `P_x(ρ, T) = det (1 - T F_x ∣ V)` of a Weil representation at a point
`x` of the curve. -/
noncomputable def localPolynomial (x : C) : Polynomial (PadicAlgCl l) :=
  (ρ (W.frobenius x)).charpolyRev

/-- The multiset of local Frobenius eigenvalues of `ρ` at `x`, the inverse roots of
`AlgebraicGeometry.WeilGroup.localPolynomial`. -/
noncomputable def localEigenvalues (x : C) : Multiset (PadicAlgCl l) :=
  (ρ (W.frobenius x)).charpoly.roots

variable (ι : PadicAlgCl l →+* ℂ)

/-- Blueprint `sk-d-real-weights`: Local weights and reality.

`ρ` is punctually `ι`-pure of weight `w` if every local Frobenius eigenvalue at every closed
point has `ι`-weight `w`. -/
def IsPunctuallyPure (w : ℝ) : Prop :=
  ∀ x ∈ C.finitePoints, ∀ α ∈ W.localEigenvalues l ρ x, weight ι (C.pointNorm x) α = w

/-- Blueprint `sk-d-real-weights`: Local weights and reality.

`ρ` has weights at most `w` if every local Frobenius eigenvalue at every closed point has
`ι`-weight at most `w`. -/
def HasWeightsAtMost (w : ℝ) : Prop :=
  ∀ x ∈ C.finitePoints, ∀ α ∈ W.localEigenvalues l ρ x, weight ι (C.pointNorm x) α ≤ w

/-- Blueprint `sk-d-real-weights`: Local weights and reality.

`ρ` is `ι`-real if `ι P_x(ρ, T)` has real coefficients for every closed point `x`;
equivalently, every complex local eigenvalue multiset is stable under complex conjugation. -/
def IsReal : Prop :=
  ∀ x ∈ C.finitePoints, ∀ n : ℕ, (starRingEnd ℂ) (ι ((W.localPolynomial l ρ x).coeff n)) =
    ι ((W.localPolynomial l ρ x).coeff n)

/-- Blueprint `sk-d-real-detweights`: Determinant weights and weight blocks.

`ρ` has determinant weight `γ`, written `dw_ι(ρ) = γ`, if the determinant character is
punctually `ι`-pure of weight `rank ρ * γ`. By `sk-p-real-rankone` a nonzero irreducible `ρ`
has exactly one determinant weight. -/
def HasDetWeight (γ : ℝ) : Prop :=
  ∀ x ∈ C.finitePoints, weight ι (C.pointNorm x) (LinearMap.det (ρ (W.frobenius x)))
    = Module.finrank (PadicAlgCl l) V * γ

variable {W l ρ}

/-- Blueprint `sk-p-real-operations`: Local Frobenius polynomials.

The local polynomial at `x` is `det (1 - T ρ g ∣ V)` for *every* member `g` of the
Frobenius conjugacy class of degree `e_x` supplied by `x`: a characteristic polynomial is
invariant under conjugation, so the local polynomial of `sk-d-real-weights` is well defined
and is computed by the representation of `sk-i-real-sheaves`. -/
theorem localPolynomial_eq_charpolyRev_of_isConj {x : C} {g : W.carrier}
    (hg : IsConj (W.frobenius x) g) :
    W.localPolynomial l ρ x = (ρ g).charpolyRev := by
  sorry

end WeilGroup

variable {α : Type*} [Fintype α]

/-- Blueprint `sk-d-real-detweights`: Determinant weights and weight blocks.

The rank `N_γ = ∑_{dw(a) > γ} r_a` of the constituents of determinant weight above `γ`, for a
family of constituents indexed by `α` with determinant weights `dw` and ranks `r`. -/
noncomputable def rankAbove (dw : α → ℝ) (r : α → ℕ) (γ : ℝ) : ℕ :=
  ∑ a ∈ {a | γ < dw a}, r a

/-- Blueprint `sk-d-real-detweights`: Determinant weights and weight blocks.

The weight sum `B_γ = ∑_{dw(a) > γ} r_a dw(a)` above `γ`, for a family of constituents
indexed by `α` with determinant weights `dw` and ranks `r`. -/
noncomputable def weightSumAbove (dw : α → ℝ) (r : α → ℕ) (γ : ℝ) : ℝ :=
  ∑ a ∈ {a | γ < dw a}, (r a : ℝ) * dw a

end AlgebraicGeometry
