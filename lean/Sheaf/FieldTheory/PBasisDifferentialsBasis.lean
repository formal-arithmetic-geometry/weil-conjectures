/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Differentials of a p-basis

Source: Stacks Project, More on Algebra, Definition 07P1 and Lemma 07P2, implication
(a) implies (b) (blueprint: lem-weil-pbc-p-basis-differentials-basis).
-/

@[expose] public section

universe u v w

namespace KaehlerDifferential

/-- Source: Stacks Project, Tags 07P1 and 07P2, implication (a) implies (b).
(blueprint: lem-weil-pbc-p-basis-differentials-basis)

The differentials of a p-basis form a basis of the relative differentials.

Proof:
1. Put B = kK^p. The universal k-derivation kills k and p-th powers by Leibniz in
   characteristic p. Its kernel is a subfield (the inverse rule follows from d(aa⁻¹) = 0),
   so it kills B (def-weil-pbc-kahler-differentials).
2. Evaluate B[X_i] at t_i (def-weil-pbc-mv-polynomial-ring). Modulo the ideal generated
   by X_i^p - t_i^p, reduction of exponents shows the bounded monomials span. Their
   images are a basis by hypothesis, hence evaluation induces K ≅ B[X_i]/(X_i^p-t_i^p).
   Each polynomial uses finitely many variables, so this works for arbitrary I.
3. Polynomial differentials are free on dX_i
   (lem-weil-pbc-polynomial-ring-kahler-basis-any-variables). The quotient conormal
   sequence (lem-weil-pbc-jacobi-zariski-differential-maps) has zero first map: each
   defining relation has zero differential, and Leibniz gives zero for every relation
   after tensoring with K. Thus Ω[K/B] is free on dt_i.
4. The first exact sequence for k → B → K
   (lem-weil-pbc-kahler-differentials-first-exact-sequence) identifies Ω[K/k] with Ω[K/B]:
   its first map is zero since d kills B, and its second map is surjective with zero
   kernel. It sends dt_i to dt_i, giving the desired basis, also for empty I. -/
theorem exists_basis_differentials_of_pBasis
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP K p]
    {I : Type w} (t : I → K)
    (hmon : ∃ b : Module.Basis {E : I →₀ ℕ // ∀ i : I, E i < p}
        (IntermediateField.adjoin k (Set.range (fun x : K => x ^ p))) K,
      ∀ E, b E = E.val.prod (fun i e => t i ^ e)) :
    ∃ b : Module.Basis I K (KaehlerDifferential k K),
      ∀ i : I, b i = D k K (t i) := by
  sorry

end KaehlerDifferential
