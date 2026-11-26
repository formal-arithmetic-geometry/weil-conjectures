/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.Mathlib.RingTheory.Regular.ProjectiveDimension

/-!
# Regularity descends along flat local homomorphisms

If `R → S` is a flat local homomorphism of Noetherian local rings with `S` regular, then `R` is
regular.

## Implementation details

The statement is reduced, by lifting both rings with `ULift`, to `IsRegularLocalRing.of_flat`,
which needs an algebra structure with both rings in one universe.

## References

* [Stacks, Tag 00OF]
-/

@[expose] public section

universe u v

namespace IsRegularLocalRing

/-- If `φ : R → S` is a flat local homomorphism of Noetherian local rings and `S` is a regular
local ring, then `R` is a regular local ring. -/
theorem of_ringHom_flat {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsNoetherianRing R] [IsRegularLocalRing S] (φ : R →+* S) [IsLocalHom φ] (hφ : φ.Flat) :
    IsRegularLocalRing R := by
  let φ' : ULift.{v} R →+* ULift.{u} S := φ.ulift
  let : IsLocalRing (ULift.{v} R) := ULift.ringEquiv.symm.isLocalRing
  let : IsNoetherianRing (ULift.{v} R) :=
    isNoetherianRing_of_ringEquiv R ULift.ringEquiv.symm
  let : IsRegularLocalRing (ULift.{u} S) := of_ringEquiv ULift.ringEquiv.symm
  let : Algebra (ULift.{v} R) (ULift.{u} S) := φ'.toAlgebra
  have : IsLocalHom φ' := by
    dsimp [φ', RingHom.ulift]
    infer_instance
  have : IsLocalHom (algebraMap (ULift.{v} R) (ULift.{u} S)) := ‹IsLocalHom φ'›
  have : Module.Flat (ULift.{v} R) (ULift.{u} S) :=
    (RingHom.Flat.ulift_iff).mpr hφ
  have : IsRegularLocalRing (ULift.{v} R) := of_flat (S := ULift.{u} S)
  exact of_ringEquiv ULift.ringEquiv

end IsRegularLocalRing
