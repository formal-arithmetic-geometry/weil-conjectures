/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.RingTheory.SyntomicPrincipalLocalizationFibreTransport

/-!
# Syntomic hypotheses after principal localization

Principal localization outside a prime preserves the complete-intersection fibre hypothesis.

## Implementation details

The prime `q` extends to a prime of `S_g` contracting to `q`, since no power of `g` lies in `q`.
The fibre of `S_g` is the localization of the old fibre at `1 ⊗ g`, and the witness is
transported using stability of global complete intersections under principal localization.

## References

* [Stacks, Tag 00SY], proof of (3) ⇒ (2)
* [Stacks, Tag 00SA]
-/

@[expose] public section

universe u v
namespace Algebra

/-- If the fibre of `R → S` is a global complete intersection near the fibre prime of `q` and
`g ∉ q`, then there is a prime `q₁` of `S_g` contracting to `q` such that the fibre of `R → S_g`
is a global complete intersection near the fibre prime of `q₁`. -/
theorem exists_completeIntersection_fibre_away
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S)
    (g : S) (hg : g ∉ q.asIdeal)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ q₁ : PrimeSpectrum (Localization.Away g),
      q₁.comap (algebraMap S (Localization.Away g)) = q ∧
      ∃ h : (q₁.asIdeal.comap (algebraMap R (Localization.Away g))).Fiber
          (Localization.Away g),
        h ∉ (PrimeSpectrum.preimageEquivFiber R (Localization.Away g)
          (q₁.comap (algebraMap R (Localization.Away g))) ⟨q₁, rfl⟩).asIdeal ∧
        IsGlobalCompleteIntersection
          (q₁.asIdeal.comap (algebraMap R (Localization.Away g))).ResidueField
          (Localization.Away h) := by
  have hq : q ∈ Set.range (PrimeSpectrum.comap
      (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact hg
  obtain ⟨q₁, hq₁⟩ := hq
  refine ⟨q₁, hq₁, ?_⟩
  exact exists_completeIntersection_fibre_transport q g hg q₁ hq₁ hci

end Algebra
