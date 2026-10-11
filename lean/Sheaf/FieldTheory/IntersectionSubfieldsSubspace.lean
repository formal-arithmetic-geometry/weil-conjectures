/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Pi

/-!
# Nonzero intersections of a subspace with a directed family of subfields

Source: Stacks Project, More on Algebra, Lemma 15.47.3, Tag 07P3
(blueprint: lem-weil-pbc-intersection-subfields-subspace).
-/

@[expose] public section

universe u v w

namespace IntermediateField

/-- For a nonempty downward directed family of intermediate fields whose intersection is the
base field, a linear subspace of `Kⁿ` contains a nonzero vector over the base field exactly when
it contains a nonzero vector over every field of the family.

Source: Stacks Project, More on Algebra, Lemma 15.47.3, Tag 07P3
(blueprint: lem-weil-pbc-intersection-subfields-subspace).

Proof:
1. A nonzero vector over `k` lies over every intermediate field, giving the forward implication.
2. For the converse, induct on `n`. For `n = 1`, a nonzero vector in the subspace makes the
   subspace all of `K`. Nonemptiness of the index type supplies such a vector, so `1` works.
3. For larger `n`, let `W` be the subspace of tails of vectors in `V` with first coordinate zero.
   A nonzero vector of `W` over `k` finishes the proof by adjoining a leading zero. Otherwise,
   the induction hypothesis gives an index `a` for which `W` has zero intersection over `L a`.
4. Choose a nonzero vector of `V` over `L a`. Its first coordinate is nonzero, so divide by it
   to obtain `v` with first coordinate `1`. Subtracting the first coordinate times `v` from
   any vector of `V` over `L a` shows that this intersection is the line `(L a) v`.
   For any `L b ≤ L a`, a nonzero vector over `L b` therefore normalizes to the same `v`,
   so all coordinates of `v` lie in `L b`.
5. For any index `c`, downward directedness supplies `b` with `L b ≤ L a ⊓ L c`.
   Thus every coordinate of `v` lies in every `L c`, hence in their intersection `k`.
   Its first coordinate is `1`, so it is the required nonzero vector. -/
theorem exists_ne_zero_mem_base_iff_forall_mem_intermediateField
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {ι : Type w} [Nonempty ι] (L : ι → IntermediateField k K)
    (h_inter : (⨅ a, L a) = ⊥)
    (h_directed : ∀ a b : ι, ∃ c : ι, L c ≤ L a ⊓ L b)
    (n : ℕ) (hn : 1 ≤ n) (V : Submodule K (Fin n → K)) :
    (∃ x : Fin n → K, x ∈ V ∧ x ≠ 0 ∧ ∀ i, x i ∈ (⊥ : IntermediateField k K)) ↔
      ∀ a : ι, ∃ x : Fin n → K, x ∈ V ∧ x ≠ 0 ∧ ∀ i, x i ∈ L a := by
  sorry

end IntermediateField
