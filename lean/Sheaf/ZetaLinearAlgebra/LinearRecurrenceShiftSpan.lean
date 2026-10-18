/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# A linear recurrence bounds the span of the shifted sequences

Source: the Weil conjectures blueprint, chapter `sec-zeta-weil`, unit `sk-prop-criterion`,
`prop-weil-rationality-criterion.proof.md`, third paragraph, final sentences
(blueprint: lem-weil-linear-recurrence-shift-span); Milne, Lectures on Etale Cohomology,
p. 157, Bourbaki's Exercise 3(d), stated without proof.
-/

@[expose] public section

universe u

namespace LinearRecurrence

/-- An order-`d` recurrence valid from index `m` puts every shift in the span of the first
`m + d` shifts. Their full span is finite-dimensional and has dimension at most `m + d`.
The recurrence uses `IsSolution` on the tail starting at `m`, with coefficients `-a i`.

Source: the Weil conjectures blueprint, `sec-zeta-weil/sk-prop-criterion`,
`prop-weil-rationality-criterion.proof.md`, third paragraph, final sentences;
Milne, Lectures on Etale Cohomology, p. 157, Bourbaki's Exercise 3(d), stated without proof
(blueprint: lem-weil-linear-recurrence-shift-span).

Proof plan:
1. For `j ≥ m`, apply the scalar recurrence at `j + s` for every coordinate `s`.
   Coordinatewise operations give `R (j + d) = -∑ i : Fin d, a i • R (j + i)`.
2. Put `W = span K {R 0, ..., R (m + d - 1)}`. By strong induction on `k`, every
   `R k` belongs to `W`: it is a generator when `k < m + d`; otherwise take `j = k - d`
   in the identity above. Each index `k - d + i` is less than `k`, so closure under finite
   sums, scalar multiplication and negation finishes the induction.
3. The span `V` of all shifts equals `W`, by the smallest-subspace characterization of
   `Submodule.span`. Every element of `W` is a linear combination of its `m + d` generators:
   these combinations form a submodule containing those generators. Hence `V` is
   finite-dimensional, using the sequence-subspace and finite-dimensional-subspace definitions.
4. Apply `exists_linearIndependent'` (lem-weil-span-independent-subfamily) to the initial
   family. Its independent subfamily has the same span `V`. By `finrank_span_eq_card`
   (lem-weil-dimension-span-independent-family), the dimension of `V` is the size of this
   subfamily, which is at most `m + d`. No independence of the original rows is assumed. -/
theorem shift_span_bound {K : Type u} [Field K] (m d : ℕ) (hd : 1 ≤ d)
    (a : Fin d → K) (c : ℕ → K)
    (hrec : (⟨d, fun i ↦ -a i⟩ : LinearRecurrence K).IsSolution (fun n ↦ c (n + m))) :
    (∀ j : ℕ, (fun s : ℕ ↦ c (j + s)) ∈
      Submodule.span K (Set.range (fun i : Fin (m + d) ↦ fun s : ℕ ↦ c (i.val + s)))) ∧
    FiniteDimensional K
      (Submodule.span K (Set.range (fun j : ℕ ↦ fun s : ℕ ↦ c (j + s)))) ∧
    Module.finrank K
      (Submodule.span K (Set.range (fun j : ℕ ↦ fun s : ℕ ↦ c (j + s)))) ≤ m + d := by
  sorry

end LinearRecurrence
