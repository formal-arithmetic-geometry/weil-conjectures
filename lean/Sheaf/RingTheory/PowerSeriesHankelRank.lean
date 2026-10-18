/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import WeilConjectures.ZetaLinearAlgebra.RationalityCriterion
public import Mathlib.Data.ENat.Lattice

/-!
# The Hankel rank of a formal power series

Source: the Weil conjectures blueprint, chapter `sec-zeta-weil`, unit `sk-def-roots`,
definition `def-weil-hankel-matrix` (blueprint: def-weil-hankel-matrix).

The matrix itself is the existing `PowerSeries.hankel`. Its rank is the supremum of the
ranks of all finite square submatrices, with their rows and columns listed in increasing order.
-/

@[expose] public section

universe u

namespace PowerSeries

/-- The Hankel rank is the supremum in `ℕ∞` of the ranks over `K` of all finite square
submatrices of `hankel C`. An order embedding `Fin k ↪o ℕ` lists `k` distinct indices in
increasing order, including the empty list when `k = 0`.
Source: Weil conjectures blueprint, `sk-def-roots`, definition `def-weil-hankel-matrix`
(blueprint: def-weil-hankel-matrix). -/
noncomputable def hankelRank {K : Type u} [Field K] (C : PowerSeries K) : ℕ∞ :=
  ⨆ x : Σ k : ℕ, (Fin k ↪o ℕ) × (Fin k ↪o ℕ),
    (((hankel C).submatrix x.2.1 x.2.2).rank : ℕ∞)

/-- The Hankel rank is finite exactly when the ranks of the finite square submatrices are
bounded. Source: Weil conjectures blueprint, `sk-def-roots`, definition
`def-weil-hankel-matrix` (blueprint: def-weil-hankel-matrix).

Proof: unfold `hankelRank` and apply `ENat.iSup_natCast_lt_top` to the natural-valued
family indexed by the size and the two increasing lists of indices. Boundedness of its range
is precisely the existence of a natural number bounding every such rank. -/
theorem hankelRank_lt_top_iff {K : Type u} [Field K] (C : PowerSeries K) :
    hankelRank C < ⊤ ↔
      ∃ R : ℕ, ∀ (k : ℕ) (r s : Fin k ↪o ℕ),
        ((hankel C).submatrix r s).rank ≤ R := by
  sorry

end PowerSeries
