/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.ProEtale.WContractible

/-!
# Retractions from closed subsets of connected components

Source: Stacks Project, Tag 09AZ, proof of (3) implies (1), restriction to the closed
component subset (blueprint: lem-weil-pbc-wlocal-closed-component-retraction).
-/

@[expose] public section

universe u v

/-- A map of w-local rings identifying prime stalks and preserving closed points admits a
retraction whenever a closed subset of source-spectrum components maps bijectively onto the
target-spectrum components.

Source: Stacks Project, Tag 09AZ, proof of (3) implies (1).
(blueprint: lem-weil-pbc-wlocal-closed-component-retraction)

Proof: equip `S` with the `R`-algebra structure induced by `g` (def-weil-pbc-w-local).
The canonical map is then `g`. Its local ring maps are bijective by `hstalk`
(def-weil-pbc-localization-at-prime). The closed-point condition is `hclosed`.
Surjectivity of `hbij` gives a component in `T` over each component of `Spec R`, and
injectivity gives equality of two components of `T` with the same image. Apply the
closed-component restriction retraction theorem
(lem-weil-pbc-wlocal-isClosed-bijOn-retraction), obtaining `s` with `s.comp g = RingHom.id R`.
For different ring universes, carry out the same construction in their common maximum
universe by lifting the rings and transport the resulting retraction back. -/
theorem RingHom.exists_retraction_of_closed_component_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsWLocalRing R] [IsWLocalRing S] (g : R →+* S)
    (hstalk : g.BijectiveOnStalks)
    (hclosed : ∀ y ∈ closedPoints (PrimeSpectrum S),
      PrimeSpectrum.comap g y ∈ closedPoints (PrimeSpectrum R))
    (T : Set (ConnectedComponents (PrimeSpectrum S))) (hT : IsClosed T)
    (hbij : Function.Bijective
      (fun t : T ↦ (PrimeSpectrum.continuous_comap g).connectedComponentsMap t.val)) :
    ∃ s : S →+* R, s.comp g = RingHom.id R := by
  sorry
