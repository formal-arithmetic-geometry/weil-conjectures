/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J5
-/
module

public import Sheaf.AlgebraicTopology.OrderedJoinCosetChains

/-! # Erasure and boundary -/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators

namespace AlgebraicTopology.OrderedJoin.CosetComparison

variable {G : Type u} [Group G]

/-- Forgetting colors commutes with alternating deletion in every integer degree.

Source: ordered-coset comparison, calculation 6 of the agent expansion of
six-functors direct-images paragraph (3)
(blueprint: lem-sfb-ordered-join-coset-erasure-boundary).

Proof: It suffices to check basis symbols, since both sides are integer-linear.
The list produced by erasure enumerates exactly the face's colors in increasing
order. The position of color i in this list is the number of colors less than i,
so its deletion sign is precisely positionSign. Erasing color i before forming
the list gives the same list as removing that position afterwards. Thus both
sides are the same signed sum, reindexed from the finite set of colors to their
positions in the list. A singleton gives the empty tuple on both sides. The
empty face has no deletions and both sides vanish; in degrees with no symbols
the claim follows by extensionality from the empty basis. -/
theorem cosetErasureBoundary (H : Subgroup G) {n : ℕ}
    (a : Fin (n + 1) → G) :
    (∀ q : ℤ,
      (tupleBoundary G q (q - 1)).comp (erasure H a q) =
        (erasure H a (q - 1)).comp (boundary (Coset H a) q (q - 1))) := by sorry

end AlgebraicTopology.OrderedJoin.CosetComparison
