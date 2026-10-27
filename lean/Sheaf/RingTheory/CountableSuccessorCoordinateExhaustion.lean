/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Sheaf.RingTheory.CoordinateSubmodule
public import Mathlib.Data.Set.Countable

/-!
# Countable successor closure and coordinate exhaustion

Source: Stacks Project, Algebra, Tag 058X, `theorem-kaplansky-direct-sum`,
proof lines 20511–20552, regrouping the support construction into successor stages
(blueprint: lem-trf-countable-successor-coordinate-exhaustion).

The two definitions give the prescribed stages and their union, with no choices.
The theorem states their countability, closure, and finite-support exhaustion.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace DirectSum

/-- The prescribed successor stages: start with `C`, then adjoin `F j` for each
index already present. Source: Stacks Project, Algebra, Tag 058X,
`theorem-kaplansky-direct-sum`, proof lines 20511–20552, successor-stage regrouping
(blueprint: lem-trf-countable-successor-coordinate-exhaustion). -/
def coordinateClosureStage {J : Type v} (C : Set J) (F : J → Set J) : ℕ → Set J
  | 0 => C
  | k + 1 => coordinateClosureStage C F k ∪ ⋃ j ∈ coordinateClosureStage C F k, F j

/-- The union of all prescribed successor stages. Source: Stacks Project, Algebra,
Tag 058X, `theorem-kaplansky-direct-sum`, proof lines 20511–20552
(blueprint: lem-trf-countable-successor-coordinate-exhaustion). -/
def coordinateClosure {J : Type v} (C : Set J) (F : J → Set J) : Set J :=
  ⋃ k, coordinateClosureStage C F k

/-- Countable successor closure and exhaustion by coordinate stages.

Source: Stacks Project, Algebra, Tag 058X, `theorem-kaplansky-direct-sum`,
proof lines 20511–20552, successor-stage regrouping
(blueprint: lem-trf-countable-successor-coordinate-exhaustion).

Proof plan:
1. The recursion includes each stage in its successor. Iteration gives monotonicity;
   each stage lies in the union, so the union contains the initial set.
2. Induct on the stage. Use the restricted countable union and binary union clauses of
   `lem-trf-countable-unions` (`Set.Countable.biUnion` and `Set.Countable.union`).
3. Apply its sequence clause (`Set.countable_iUnion`) to obtain countability of the union.
4. If `j` belongs to the union, it belongs to some stage, so `F j` lies in the next stage
   and hence in the union.
5. Induct on a finite subset of the union: the empty set lies in stage zero; for an
   insertion, take the maximum of the old stage and a stage containing the inserted index.
6. By `def-weil-pbc-direct-sum-modules`, every direct-sum vector has finite support.
   By `def-trf-coordinate-submodule`, membership means that this support is contained in
   the index set. Step 5 puts the support of a vector on the union in one stage.
   Conversely, stage membership implies membership on the union. The zero vector lies in
   stage zero. No generation or countability of the ring or modules is used.
-/
theorem countable_successor_coordinate_exhaustion
    {J : Type v} (C : Set J) (F : J → Set J)
    (hC : C.Countable) (hF : ∀ j : J, (F j).Countable)
    (R : Type u) [CommRing R] (N : J → Type w)
    [∀ j : J, AddCommGroup (N j)] [∀ j : J, Module R (N j)] :
    Monotone (coordinateClosureStage C F) ∧
      (∀ k : ℕ, (coordinateClosureStage C F k).Countable) ∧
      (coordinateClosure C F).Countable ∧
      C ⊆ coordinateClosure C F ∧
      (∀ j ∈ coordinateClosure C F, F j ⊆ coordinateClosure C F) ∧
      (∀ E : Set J, E.Finite → E ⊆ coordinateClosure C F →
        ∃ k : ℕ, E ⊆ coordinateClosureStage C F k) ∧
      (coordinateSubmodule R J N (coordinateClosure C F) : Set (⨁ j, N j)) =
        ⋃ k : ℕ, (coordinateSubmodule R J N (coordinateClosureStage C F k) :
          Set (⨁ j, N j)) := by
  sorry

end DirectSum
