/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import WeilConjectures.RingTheory.RegularRingEquiv

/-!
# Transporting the G-ring property through a ring isomorphism

The G-ring property is invariant under ring isomorphism.

## Implementation details

A ring isomorphism `R ≃+* S` induces isomorphisms of the prime localizations and of their adic
completions, compatible with the completion maps, and regularity of ring maps transports along
these. Fields and algebras in different universes are first lifted to a common universe.

## References

* [Stacks, Tag 07GH]
* [Stacks, Tag 07PV] (first paragraph)
-/

@[expose] public section

universe u v

/-- The G-ring property is invariant under ring isomorphism: if `R ≃+* S` and `R` is a G-ring,
then so is `S`. -/
theorem isGRing_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (hR : IsGRing R) : IsGRing S := by
  let : IsNoetherianRing R := hR.1
  refine ⟨isNoetherianRing_of_ringEquiv R e, ?_⟩
  intro p hp
  let q : Ideal R := p.comap e.toRingHom
  let : q.IsPrime := Ideal.comap_isPrime e.toRingHom p
  let a : Localization.AtPrime q ≃+* Localization.AtPrime p :=
    Localization.localRingEquiv q p e rfl
  obtain ⟨b, hb⟩ := AdicCompletion.exists_ringEquiv
    (IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)) a
    (IsLocalRing.map_ringEquiv_maximalIdeal a).symm
  exact RingHom.IsRegular.of_ringEquiv _ _ a b hb (hR.2 q)
