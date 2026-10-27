/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Sheaf.Paper.CodegreePolygon
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Uniform strict polygon gap for integral codegrees

Source: Morrison, *GIT Constructions of Moduli Spaces of Stable Curves and Maps*,
Section 2.4, Lemma 6 and Figure 2, pp. 11–12, with the corrected factor two and
quantitative strict refinement recorded in the DAG
(blueprint: lem-sfb-strict-codegree-polygon-gap).

The cost and minimum are imported from their definition-owning module.
Their formulas and names are unchanged.
-/

@[expose] public section

open scoped BigOperators

namespace Gieseker

/-- A positive gap depending only on `N,d`, uniform over integral codegrees and
normalized decreasing weights. Source: Morrison, Section 2.4, Lemma 6 and Figure 2,
pp. 11–12, corrected factor-two estimate with the DAG's quantitative strict refinement
(blueprint: lem-sfb-strict-codegree-polygon-gap).

Proof plan, following the eight steps of the node:
1. Put `n=N-1`, `α=d/n`, `δ=1/n`, and choose `η=1/(N*n^2)`. The deficits
   `D_i=α*i-e_i` vanish at both endpoints and are at least `δ` in the interior,
   since `d*i-n*e_i` is a positive integer. Normalization implies `w_0 ≥ 1/n`.
2. Use [lem-sfb-finite-convex-minorant-chain] to select a lower convex contact
   chain with interpolant `v ≤ w`. Put `S=∑ v_i ≤ 1`.
3. Sum the inequalities between the first `i` and last `n-i` adjacent differences.
   This gives `v_i ≤ (1-i/n)*w_0`, hence `S ≤ N*w_0/2`.
4. On each chain edge the trapezoid identity and telescoping give
   `C_α=α*(2*S-w_0) ≤ 2*d*S/N ≤ 2*d/N`.
5. If the chain has an interior vertex, every edge has an interior endpoint.
   Thus `C_α-C_e ≥ δ*w_0 ≥ δ/n ≥ η`, which gives the bound.
6. Otherwise the chain consists of the two endpoints. Put `s=2/N-w_0 ≥ 0`.
   Its cost is `2*d/N-d*s`. If `s ≥ δ/(d*N*n)`, the required gap follows.
7. In the remaining case set `A_k=d*w_k-α*(n-k)*w_0` on interior indices.
   Their sum is `d*N*s/2`, so one is at most `d*N*s/(2*(n-1))`.
8. Insert that index `k`. Its cost is `d*w_0+A_k-D_k*w_0`, at most
   `2*d/N+δ/(2*n*(n-1))-δ/n ≤ 2*d/N-δ/(2*n) ≤ 2*d/N-η`.
   The minimum is no larger than this cost. The single chosen `η` works for all `e`.
-/
theorem exists_uniform_strict_codegree_polygon_gap (N : ℕ) (d : ℤ)
    (hN : 3 ≤ N) (hd : 1 ≤ d) :
    ∃ η : ℝ, 0 < η ∧ ∀ (e : Fin N → ℤ),
      e ⟨0, by omega⟩ = 0 →
      e ⟨N - 1, by omega⟩ = d →
      (∀ i : Fin N, 0 ≤ e i ∧ e i ≤ d) →
      (∀ i : Fin N, 0 < i.val → i.val < N - 1 →
        (e i : ℝ) < (d : ℝ) * (i.val : ℝ) / ((N : ℝ) - 1)) →
      ∀ (w : Fin N → ℝ), Antitone w →
        w ⟨N - 1, by omega⟩ = 0 → (∑ i : Fin N, w i) = 1 →
        codegreePolygonMinimum e w ≤ 2 * (d : ℝ) / (N : ℝ) - η := by
  sorry

end Gieseker
