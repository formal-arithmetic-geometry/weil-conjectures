/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.KrullDimension.GoingDown

/-!
# Faithfully flat local maps do not lower Krull dimension

A faithfully flat local homomorphism of local rings `A → B` satisfies `dim A ≤ dim B`.

## References

* [Stacks, Tag 00OH]
* [Stacks, Tag 00HS]
* [Stacks, Tag 00HQ]
-/

@[expose] public section

universe u v

namespace RingHom

/-- A faithfully flat local homomorphism of local commutative rings does not lower Krull
 dimension. -/
theorem ringKrullDim_le_of_faithfullyFlat_of_isLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : f.FaithfullyFlat) :
    ringKrullDim A ≤ ringKrullDim B := by
  let := f.toAlgebra
  have : Module.Flat A B := hf.flat
  exact ringKrullDim_le_of_goingDown_of_surjective f
    (Algebra.HasGoingDown.of_flat)
    (FaithfullyFlat.iff_flat_and_comap_surjective.mp hf).2

end RingHom
