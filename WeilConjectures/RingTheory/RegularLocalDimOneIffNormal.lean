/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regularity and normality for one-dimensional Noetherian local rings

A one-dimensional Noetherian local ring is regular exactly when it is a normal domain.

## Implementation details

A regular local ring of dimension one is a discrete valuation ring, hence a normal domain.
Conversely, a one-dimensional normal local domain is a discrete valuation ring, whose maximal
ideal is principal, so it is regular.

## References

* [Stacks, Tag 00PD] ((3) ⇔ (5))
-/

@[expose] public section

universe u

namespace IsRegularLocalRing

/-- A one-dimensional Noetherian local ring is regular exactly when it is a normal domain. -/
theorem iff_isDomain_and_isIntegrallyClosed_of_dim_one (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1) :
    IsRegularLocalRing A ↔ IsDomain A ∧ IsIntegrallyClosed A := by
  constructor
  · intro hreg
    let : IsRegularLocalRing A := hreg
    let : IsDiscreteValuationRing A := IsRegularLocalRing.isDiscreteValuationRing A hdim
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hdom, hclosed⟩
    let : IsDomain A := hdom
    let : IsIntegrallyClosed A := hclosed
    apply IsRegularLocalRing.of_isIntegrallyClosed A
    rw [hdim]

end IsRegularLocalRing
