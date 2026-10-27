/-
Copyright (c) 2026 The Weil SHEAF project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Weil SHEAF project
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Coercivity from a compact remainder estimate

Source: Demailly, Complex Analytic and Differential Geometry, VI §2, proof of
Corollary (2.4)(ii), estimate (2.5), printed p.290. The abstract Hilbert-space
formulation and normalized-sequence argument are isolated in the project DAG
(blueprint: lem-sfb-compact-remainder-coercivity).
-/

@[expose] public section

universe u v w

open scoped Topology

namespace ContinuousLinearMap

/-- A compact remainder estimate gives a uniform norm estimate on the orthogonal
complement of the kernel. Compactness is stated in precisely its sequential sense:
every norm-bounded sequence has a subsequence whose image under `J` converges in `Z`.

Source: Demailly, Complex Analytic and Differential Geometry, VI §2, proof of
Corollary (2.4)(ii), estimate (2.5), printed p.290; the abstract argument below was
isolated by the project (blueprint: lem-sfb-compact-remainder-coercivity).

Proof plan (the five elementary steps of the node):
1. If every positive bound fails, choose `x_n` in the kernel complement with
   `‖x_n‖ > n * ‖T x_n‖` for positive `n`. Normalize to unit vectors `v_n` in that
   complement. Then `‖T v_n‖ < 1 / n`, so `T v_n` tends to zero.
2. Apply the sequential compactness hypothesis to this bounded sequence. Extract
   strictly increasing indices and write the subsequence as `u_j`, with `J u_j`
   converging to `z`. Its norms remain one and `T u_j` still tends to zero.
3. Apply the assumed estimate to `u_i - u_j`. Its norm is at most `C` times the sum
   of `‖T u_i‖`, `‖T u_j‖`, `‖J u_i - z‖`, and `‖J u_j - z‖`. Make each term less
   than `ε / (4 * C)` to prove that `u_j` is Cauchy.
4. Completeness of `E` gives a limit `u`. The reverse triangle inequality gives
   `‖u‖ = 1`, and boundedness of `T` gives `T u = 0`, so `u` belongs to the kernel.
5. Orthogonality gives `inner ℝ u (u_j) = 0`. Thus `‖u_j - u‖ ^ 2 = 2`, which
   contradicts convergence to `u`. Therefore some positive uniform bound exists. -/
theorem exists_pos_norm_le_on_orthogonal_ker_of_compact_remainder
    {E : Type u} {F : Type v} {Z : Type w}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : E →L[ℝ] F) (J : E →L[ℝ] Z)
    (hJ : ∀ x : ℕ → E, (∃ M : ℝ, ∀ n : ℕ, ‖x n‖ ≤ M) →
      ∃ (φ : ℕ → ℕ) (z : Z), StrictMono φ ∧
        Filter.Tendsto (fun n : ℕ => J (x (φ n))) Filter.atTop (nhds z))
    (hestimate : ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖x‖ ≤ C * (‖T x‖ + ‖J x‖)) :
    ∃ D : ℝ, 0 < D ∧ ∀ v : E, v ∈ T.ker.orthogonal → ‖v‖ ≤ D * ‖T v‖ := by
  sorry

end ContinuousLinearMap
