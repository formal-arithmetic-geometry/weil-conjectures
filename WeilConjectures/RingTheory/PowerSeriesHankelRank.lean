/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Data.ENat.Lattice
public import WeilConjectures.ZetaLinearAlgebra.RationalityCriterion

/-!
# Hankel rank of a formal power series

Source: the current blueprint, `sec-zeta-weil/sk-prop-criterion/def-weil-hankel-matrix.md`
(blueprint: def-weil-hankel-matrix).

The matrix itself is the existing `PowerSeries.hankel`. Its rank is defined as the supremum
of the ranks of its finite square submatrices, with increasing row and column indices.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace PowerSeries

/-- The supremum, in the extended natural numbers, of the ranks of the finite square
submatrices of the Hankel matrix. Order embeddings list the selected rows and columns
in increasing order, including the empty submatrix when the size is zero.

Source: the current blueprint, `sec-zeta-weil/sk-prop-criterion/def-weil-hankel-matrix.md`
(blueprint: def-weil-hankel-matrix). -/
def hankelRank {K : Type u} [Field K] (C : PowerSeries K) : ℕ∞ :=
  ⨆ x : Σ k : ℕ, (Fin k ↪o ℕ) × (Fin k ↪o ℕ),
    (((hankel C).submatrix x.2.1 x.2.2).rank : ℕ∞)

/-- The Hankel rank is finite exactly when the finite square submatrix ranks admit one
uniform natural-number bound.

Source: the current blueprint, `sec-zeta-weil/sk-prop-criterion/def-weil-hankel-matrix.md`,
and the finiteness clause of the DAG definition (blueprint: def-weil-hankel-matrix).

Proof: apply `ENat.iSup_natCast_lt_top` to the family of finite square submatrix ranks.
Boundedness of its range means that there is a natural number bounding every member
of that family. Unpack the sigma index into the size and the two increasing selections.
Conversely, a bound for all these selections bounds the range, so its supremum is finite.
This is the general supremum property recorded by `def-weil-extended-natural-supremum`. -/
theorem hankelRank_lt_top_iff {K : Type u} [Field K] (C : PowerSeries K) :
    hankelRank C < ⊤ ↔
      ∃ N : ℕ, ∀ (k : ℕ) (r s : Fin k ↪o ℕ),
        ((hankel C).submatrix r s).rank ≤ N := by
  let f : (Σ k : ℕ, (Fin k ↪o ℕ) × (Fin k ↪o ℕ)) → ℕ :=
    fun x => ((hankel C).submatrix x.2.1 x.2.2).rank
  rw [show hankelRank C = ⨆ x, (f x : ℕ∞) by rfl,
    ENat.iSup_natCast_lt_top]
  constructor
  · intro h
    rw [bddAbove_def] at h
    obtain ⟨N, hN⟩ := h
    refine ⟨N, ?_⟩
    intro k r s
    exact hN _ ⟨⟨k, r, s⟩, rfl⟩
  · rintro ⟨N, hN⟩
    rw [bddAbove_def]
    refine ⟨N, ?_⟩
    rintro _ ⟨⟨k, r, s⟩, rfl⟩
    exact hN k r s

end PowerSeries
