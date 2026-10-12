/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.FiniteType
import Sheaf.RingTheory.FilteredColimitAlgebrasTensorElementwise

/-! # Finite-type reduction for tensor products

Source: literature/stacks-project/algebra.tex, Algebra, Lemma 00I3
(algebra-lemma-limit-argument) (blueprint: lem-weil-pbc-tensor-finite-type-limit)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra

/-- Finite-type reduction for tensor products, clauses (1) and (2) of Stacks Algebra,
Lemma 00I3 (algebra-lemma-limit-argument).

Proof:
1. The finitely generated subalgebras of each factor form a directed system:
   adjoining the union of two finite generating sets gives a common upper bound,
   and each element belongs to the subalgebra it generates. Their filtered colimits
   are the full algebras; use `lem-weil-pbc-filtered-colimit-algebras-elementwise`.
2. For a nonzero nilpotent z with z^n = 0, first descend z to a finitely generated
   subalgebra of R with S fixed, and enlarge that stage until its nth power is zero.
   Then fix that stage and descend the element and its zero nth power to a finitely
   generated subalgebra of S. Use the representative and eventual-zero clauses of
   `lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise` twice (with tensor
   symmetry on the second pass). Each representative is nonzero because its image
   is z. Thus the smaller tensor product is not reduced.
3. For nonzero x and y with xy = 0, descend both to a common finitely generated
   R-stage with S fixed, then enlarge it until their product vanishes. Next descend
   both to a common finitely generated S-stage with that R-stage fixed, and enlarge
   it until the product vanishes. Use the same tensor-colimit node's representative
   and eventual-zero assertions. Both resulting factors stay nonzero because their
   images are x and y, so the smaller tensor product has a nonzero zero-divisor.

(blueprint: lem-weil-pbc-tensor-finite-type-limit) -/
theorem tensor_finite_type_limit
    (k : Type u) [Field k]
    (R : Type v) [CommRing R] [Algebra k R]
    (S : Type w) [CommRing S] [Algebra k S] :
    (¬ IsReduced (R ⊗[k] S) →
      ∃ (R' : Subalgebra k R) (S' : Subalgebra k S),
        Algebra.FiniteType k R' ∧ Algebra.FiniteType k S' ∧
        ¬ IsReduced (R' ⊗[k] S')) ∧
    ((∃ x y : R ⊗[k] S, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0) →
      ∃ (R' : Subalgebra k R) (S' : Subalgebra k S),
        Algebra.FiniteType k R' ∧ Algebra.FiniteType k S' ∧
        ∃ x y : R' ⊗[k] S', x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0) := by
  sorry

end Algebra
