/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.CoordinateSubmodule
public import Mathlib.Data.Set.Countable

/-!
# Countable invariant coordinate closure

Source: Stacks Project, Algebra, Tag 058X, theorem-kaplansky-direct-sum,
proof lines 20511–20552 (blueprint: lem-trf-countable-coordinate-closure).
-/

@[expose] public section

universe u v w

open DirectSum

namespace DirectSum

set_option autoImplicit false in
/-- A countable collection of countably generated summands has a countable invariant
coordinate enlargement under any endomorphism.

Source: Stacks Project, Algebra, Tag 058X, theorem-kaplansky-direct-sum,
proof lines 20511–20552 (blueprint: lem-trf-countable-coordinate-closure).

Proof:
1. Choose a countable generating sequence for each summand, and use the canonical
   direct-sum inclusions.
2. For each generator take the finite support of its image under the endomorphism;
   the union of these supports is countable for each summand.
3. Starting from the given countable set, recursively adjoin all these support sets.
   Countability is preserved at every successor stage by coding pairs of natural
   numbers, and the union over the natural stages is countable by a second pair code.
4. The endomorphism sends the coordinate submodule at stage `k` into that at stage
   `k + 1`, by linearity and the generating sequences.
5. Every element supported in the final union has finite support, hence lies at one
   stage; the preceding inclusion gives invariance of the final coordinate submodule.
-/
theorem exists_countable_coordinateSubmodule
    (R : Type u) [CommRing R] (J : Type v) (N : J → Type w)
    [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    (hN : ∀ j : J, ∃ S : Set (N j), S.Countable ∧ Submodule.span R S = ⊤)
    (f : (⨁ j, N j) →ₗ[R] (⨁ j, N j)) {C : Set J} (hC : C.Countable) :
    ∃ D : Set J, D.Countable ∧ C ⊆ D ∧
      ∀ x, x ∈ coordinateSubmodule R J N D →
        f x ∈ coordinateSubmodule R J N D := by
  sorry

end DirectSum
