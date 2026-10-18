/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.GroupTheory.RationalRank
import Sheaf.GroupTheory.TorsionfreeRationalizationInjective

/-!
# Convex subgroup chains are bounded by rational rank

Source: Temkin, *Stable modification of relative curves*, §2.1, pp. 7–8,
the convex-rank/height consequence (blueprint: lem-trf-convex-chain-rational-rank).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AddCommGroup

/-- A strict finite chain of convex subgroups of a totally ordered abelian group
has cardinality bounded by the rational rank.
Source: Temkin, *Stable modification of relative curves*, §2.1, pp. 7–8
(blueprint: lem-trf-convex-chain-rational-rank).

Proof plan:
1. For `n = 0` the cardinal on the left is zero. Otherwise choose an element of each
   `H i.succ` outside `H i.castSucc`; negate it if necessary to make it positive.
2. A totally ordered abelian group is torsion-free, since a positive integer multiple
   of a positive element is positive. If a positive multiple of a positive element lies
   in a convex subgroup, the element lies between zero and that multiple and belongs too.
3. The chosen elements give a rationally independent family after rationalization.
   Clear denominators in a rational relation and use `rationalizationMap_injective`
   (`lem-trf-torsionfree-rationalization-injective`) to obtain an integer relation in `Γ`.
   At the largest nonzero coefficient, all preceding terms lie in the preceding subgroup.
   Step 2 forces this last chosen element into that subgroup, a contradiction.
4. Apply `LinearIndependent.cardinal_lift_le_rank`
   (`lem-trf-independent-family-cardinal-dimension`) to the `Fin n`-indexed independent
   family. By `def-trf-rational-rank`, this dimension is `AddCommGroup.rationalRank Γ`. -/
theorem convexChainRationalRank
    (Γ : Type u) [AddCommGroup Γ] [LinearOrder Γ] [AddLeftMono Γ]
    (n : ℕ) (H : Fin (n + 1) → AddSubgroup Γ)
    (hconvex : ∀ i : Fin (n + 1), ∀ {h₁ h₂ x : Γ}, h₁ ∈ H i → h₂ ∈ H i →
      h₁ ≤ x → x ≤ h₂ → x ∈ H i)
    (hstrict : ∀ i : Fin n, H i.castSucc < H i.succ) :
    Cardinal.lift.{u} (Cardinal.mk (Fin n)) ≤ AddCommGroup.rationalRank Γ := by
  sorry

end AddCommGroup
