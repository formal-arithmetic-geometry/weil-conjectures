/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.GradedAlgebra.Standard
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Eventual polynomiality of standard graded Hilbert functions

Source: Stacks Project, Algebra, Tag 00K1, proposition-graded-hilbert-polynomial,
specialized to a field in degree zero (blueprint: lem-trf-standard-graded-hilbert-function).
-/

@[expose] public section

namespace GradedAlgebra.IsStandard

universe u v

/-- For a finite graded module over a standard graded algebra, the dimensions of the
homogeneous pieces are eventually given by a rational polynomial.

Source: Stacks Project, Algebra, Tag 00K1, proposition-graded-hilbert-polynomial,
specialized to a field in degree zero (blueprint: lem-trf-standard-graded-hilbert-function).

The proof follows the node's eight steps: homogeneous generators give finite-dimensional
pieces; induction on degree-one algebra generators handles the nilpotent and injective cases;
the finite-difference relation is integrated in the binomial-polynomial basis; finally the
torsion submodule and its quotient are recombined. The argument uses
`def-pc-standard-graded-algebra`, `lem-wf-affine-noetherian-components`, and
`lem-weil-pbc-noetherian-submodule-finite`.
-/
theorem exists_eventually_eq_polynomial {k : Type u} {S : Type u} {M : Type v}
    [Field k] [CommRing S] [Algebra k S] [AddCommGroup M] [Module S M] [Module k M]
    [IsScalarTower k S M] (𝒜 : ℕ → Submodule k S) (ℳ : ℕ → Submodule k M)
    [GradedAlgebra 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [Module.Finite S M] [IsStandard 𝒜] :
    (∀ n : ℕ, Module.Finite k (ℳ n)) ∧
      ∃ P : Polynomial ℚ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        (Module.finrank k (ℳ n) : ℚ) = P.eval (n : ℚ) := by
  sorry

end GradedAlgebra.IsStandard
end
