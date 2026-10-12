/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z2
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# The rank of a matrix is unchanged by field extension

Source: Milne, Lectures on Étale Cohomology, Chapter II, §27, proof of Lemma 27.9, last
sentence; Deligne, La conjecture de Weil I, "Preuve de (1.7) ⇒ (1.6)"; the blueprint of the
Weil conjectures, chapter `sec-zeta-weil`, `thm-weil-final-rationality`, proof
(blueprint: lem-weil-matrix-rank-field-extension).
-/

@[expose] public section

universe u v

namespace Matrix

/-- (blueprint: lem-weil-matrix-rank-field-extension) Let `ι : K →+* L` be a ring homomorphism
of fields and `A` an `m × n` matrix with entries in `K`, viewed over `L` by applying `ι` to
every entry (`A.map ι`). The rank (the dimension of the span of the rows,
`Matrix.rank_eq_finrank_span_row`) is the same over `L` and over `K`; equivalently, a family
of rows of `A` is linearly independent over `L` if and only if it is over `K`. Source: Milne,
LEC, §27, proof of Lemma 27.9; Deligne, Weil I, proof of (1.7) ⇒ (1.6).

Proof:
1. `ι` is injective, as `K` is a field; identify `K` with `ι(K) ⊆ L` and `K^n ⊆ L^n`
(def-pc-field-extension). The rows `r_1, …, r_m ∈ K^n` of `A` (def-weil-matrix), viewed in
`L^n`, are the rows of `A` over `L`. For `F ∈ {K, L}`, `rank_F(A)` is the dimension
(def-weil-vector-space-dimension) of the `F`-span `W_F` of the rows (def-weil-matrix-rank),
finite-dimensional as it is spanned by `m` vectors (def-weil-finite-dimensional-subspace).
2. For `F ∈ {K, L}`, `rank_F(A)` is the largest size of a set `S` of row indices with
`(r_i)_{i ∈ S}` linearly independent over `F`: by lem-weil-span-independent-subfamily some
independent subfamily spans `W_F`, and its size is `dim_F W_F` by
lem-weil-dimension-span-independent-family; conversely an independent subfamily lies in `W_F`,
so its size is at most `dim_F W_F` by lem-weil-independent-family-card-le-dimension.
3. For every `S`, `(r_i)_{i ∈ S}` is linearly independent over `L` if and only if it is over
`K`, by lem-weil-linear-independence-field-extension. This is the second clause.
4. By Steps 2 and 3 the two maxima are over the same sets, so `rank_L(A) = rank_K(A)`. -/
theorem rank_map_field_extension {K : Type u} {L : Type v} [Field K] [Field L] (ι : K →+* L)
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) :
    (A.map ι).rank = A.rank ∧
      ∀ s : Set (Fin m), LinearIndependent L (fun i : s ↦ (A.map ι).row i) ↔
        LinearIndependent K (fun i : s ↦ A.row i) := by
  sorry

end Matrix
