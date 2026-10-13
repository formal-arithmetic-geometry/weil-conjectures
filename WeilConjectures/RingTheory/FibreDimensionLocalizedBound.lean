/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-! A localized fibre comparison used by the principal-neighbourhood theorem. -/

@[expose] public section

universe u v

namespace Algebra

/-- If all points of the basic open `D(g)` have local fibre dimension at most `d`,
then every nonempty fibre after localizing away from `g` has global dimension at most `d`.
Source: Stacks Project, Algebra, Tags 00DK, 00DL and 00E4.
(blueprint: lem-weil-pbc-fibre-dimension-neighborhood-localized-bound).

The proof identifies each localized fibre with the open subspace `D(g ⊗ 1)` of the
corresponding original fibre, uses the fibre-prime order isomorphism, and then applies
the supremum formula for Krull dimension. -/
theorem localized_fibre_dimension_le_of_basicOpen
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [FiniteType R S] (g : S) (d : ℕ)
    (hV : ∀ q' : PrimeSpectrum S, q' ∈ PrimeSpectrum.basicOpen g →
      topologicalKrullDimAt
        (PrimeSpectrum.preimageEquivFiber R S (PrimeSpectrum.comap (algebraMap R S) q')
          ⟨q', rfl⟩) ≤ (d : WithBot ℕ∞)) :
    ∀ p' : PrimeSpectrum R,
      Nontrivial (p'.asIdeal.Fiber (Localization.Away g)) →
        topologicalKrullDim (PrimeSpectrum (p'.asIdeal.Fiber (Localization.Away g))) ≤
          (d : WithBot ℕ∞) := by
  sorry

end Algebra
