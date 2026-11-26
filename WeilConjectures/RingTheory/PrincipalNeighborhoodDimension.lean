/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Principal neighborhoods realizing the local dimension

Inside any principal neighborhood of a prime, a smaller principal neighborhood has dimension
equal to the local topological dimension at that prime.

## Implementation details

No finite-type or Noetherian assumption is needed.

## References

* [Stacks, Definition 0055] and the following remark
* [Stacks, Tag 00SC] (the choice of `g''` in the proof)
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- Inside any principal neighborhood of a prime, a smaller principal neighborhood
has dimension equal to the local topological dimension at that prime. -/
theorem exists_mul_away_dimension_eq
    (S : Type u) [CommRing S] (q : PrimeSpectrum S) (a : S) (ha : a ∉ q.asIdeal) :
    ∃ b : S, b ∉ q.asIdeal ∧
      topologicalKrullDim (PrimeSpectrum (Localization.Away (a * b))) =
        topologicalKrullDimAt q := by
  classical
  let N := {U : TopologicalSpace.Opens (PrimeSpectrum S) // q ∈ U}
  let : Nonempty N := ⟨⟨⊤, trivial⟩⟩
  obtain ⟨U, hU⟩ := ciInf_mem (fun V : N ↦ topologicalKrullDim V.1)
  have hmin : topologicalKrullDim U.1 = topologicalKrullDimAt q := by
    simpa [topologicalKrullDimAt, N, iInf_subtype] using hU
  obtain ⟨_, ⟨b, rfl⟩, hb, hbU⟩ :=
    isTopologicalBasis_basic_opens.isOpen_iff.mp U.1.isOpen q U.2
  have hab : q ∈ basicOpen (a * b) := by
    rw [basicOpen_mul]
    exact ⟨ha, hb⟩
  have hsub : (basicOpen (a * b) : Set (PrimeSpectrum S)) ⊆ U.1 := by
    intro x hx
    rw [basicOpen_mul] at hx
    exact hbU hx.2
  have hdim : topologicalKrullDim (basicOpen (a * b)) = topologicalKrullDimAt q := by
    apply le_antisymm
    · exact ((Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le).trans
        hmin.le
    · exact iInf₂_le (basicOpen (a * b)) hab
  let L := Localization.Away (a * b)
  have he := localization_away_isOpenEmbedding L (a * b)
  have hr := localization_away_comap_range L (a * b)
  have hd := he.isEmbedding.toHomeomorph
  refine ⟨b, hb, ?_⟩
  have heq := hd.isHomeomorph.topologicalKrullDim_eq hd
  rw [hr] at heq
  exact heq.trans hdim

end PrimeSpectrum
