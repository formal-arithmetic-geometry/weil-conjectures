/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.RingTheory.FibreDimensionLocalizedBound

/-!
# A principal neighbourhood bounding all fibre dimensions

For a finite type algebra `S` over `R`, a prime `q` of `S` whose fibre has local dimension `d`
admits `g ∉ q` such that all nonempty fibres of `R → S_g` have dimension at most `d`.

## Implementation details

The fibre point `Q` is given by `PrimeSpectrum.preimageEquivFiber`: its ideal is the kernel of
the canonical map `κ(p) ⊗[R] S → κ(q)`, `a ⊗ s ↦ ā * s̄`. Mathlib places the residue field on
the left of the tensor product.

The proof takes an open neighbourhood `V` of `q` on which all local fibre dimensions are at most
`d` (Tag 00QH), shrinks it to a basic open `D(g)` and applies
`Algebra.localized_fibre_dimension_le_of_basicOpen`.

## References

* [Stacks, Tag 00QH]
* [Stacks, Tag 00ST], proof of (3)
-/

@[expose] public section

universe u v

namespace Algebra

/-- For a finite type algebra, a prime whose fibre has local dimension `d` admits a
principal neighbourhood `D(g)` of `q` all of whose nonempty fibres have dimension at most `d`. -/
theorem exists_away_fibre_dimension_le
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [FiniteType R S] (q : PrimeSpectrum S) (d : ℕ) :
    let p := PrimeSpectrum.comap (algebraMap R S) q
    let Q := PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩
    topologicalKrullDimAt Q = (d : WithBot ℕ∞) →
      ∃ g : S, g ∉ q.asIdeal ∧
        ∀ p' : PrimeSpectrum R,
          Nontrivial (p'.asIdeal.Fiber (Localization.Away g)) →
            topologicalKrullDim (PrimeSpectrum (p'.asIdeal.Fiber (Localization.Away g))) ≤
              (d : WithBot ℕ∞) := by
  dsimp
  intro hd
  obtain ⟨V, hVopen, hqV, hdim⟩ := fibre_dimension_bounded_open_upstairs q d hd
  obtain ⟨b, ⟨g, rfl⟩, hqg, hgV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqV hVopen
  refine ⟨g, ?_, ?_⟩
  · simpa [PrimeSpectrum.mem_basicOpen] using hqg
  · exact localized_fibre_dimension_le_of_basicOpen g d (fun q' hq' ↦
      hdim q' (hgV hq'))

end Algebra
