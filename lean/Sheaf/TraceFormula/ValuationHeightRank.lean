/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Sheaf.GroupTheory.RationalRank
import Sheaf.TraceFormula.ConvexChainRationalRank
import Sheaf.TraceFormula.ValuationPrimeConvexCorrespondence

/-!
# Prime-chain length versus valuation rational rank

Source: Temkin, *Stable modification of relative curves*, §2.1, Lemma 2.1.2
(Abhyankar inequality) and Corollary 2.1.3(i) (blueprint: lem-trf-valuation-height-rank).
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped Pointwise

namespace Ideal

/-- Let `A` be a valuation ring of a field `K`. A strict chain of `n` prime ideals
has length at most the rational rank of the quotient of `Kˣ` by the unit group of `A`.
Source: Temkin, §2.1, Lemma 2.1.2 and Corollary 2.1.3(i)
(blueprint: lem-trf-valuation-height-rank).

Proof plan, following the node:
1. Order the quotient `Kˣ / A.unitGroup` by `[x] ≤ [y]` when `y / x ∈ A`.
   Multiplication by units preserves membership in `A`, so this is well defined.
   The valuation-ring alternative gives comparability; the group operations preserve
   the order. This is the order dual of Temkin's multiplicative absolute-value convention.
2. Apply `lem-trf-valuation-prime-convex-correspondence`: its canonical order
   anti-isomorphism takes the given prime chain to a decreasing convex-subgroup chain.
   Reverse the finite indexing to obtain an increasing chain with `n` strict inclusions.
3. Apply `lem-trf-convex-chain-rational-rank` to this chain. It bounds `n` by the
   Q-dimension of the rationalized quotient, which is `AddCommGroup.rationalRank`.
   Tensor symmetry identifies the definition's `ℚ ⊗[ℤ] G` with `G ⊗[ℤ] ℚ`.
-/
theorem valuationHeightLeRationalRank {K : Type u} [Field K]
    (A : ValuationSubring K) (n : ℕ) (p : Fin (n + 1) → Ideal A)
    (hp : StrictMono p) (hprime : ∀ i, (p i).IsPrime) :
    (n : Cardinal.{u}) ≤
      AddCommGroup.rationalRank (Additive (Kˣ ⧸ A.unitGroup)) := by
  sorry

end Ideal
