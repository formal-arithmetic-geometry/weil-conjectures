/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import Mathlib.Algebra.Ring.ULift

/-!
# Ind-etale ring maps across universes

The ind-étale property for ring maps between rings in different universes.

## Implementation details

The existing ind-etale predicate requires equally-sized source and target types.
Canonical `ULift` transport makes it applicable to arbitrary ring maps. The principal
ind-Zariski and weakly étale notions are exposed by `IndPrincipalZariski`.
-/

@[expose] public section
set_option autoImplicit false

universe u v

namespace RingHom

/-- A ring map is ind-etale when its canonical transport to the common universe
is ind-etale. The transported map is exactly `x ↦ ⟨f x.down⟩`. -/
def IndEtaleAcrossUniverses {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  RingHom.IndEtale (RingHom.ulift.{v, u} f)

end RingHom
