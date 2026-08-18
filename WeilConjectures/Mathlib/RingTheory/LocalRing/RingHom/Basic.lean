/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Ring homomorphisms out of a field are local

`IsLocalHom.of_field`: every ring homomorphism from a field to a nontrivial ring reflects
units, since the only non-unit of a field is `0`.
-/

@[expose] public section

/-- Every ring homomorphism from a field to a nontrivial ring is local. -/
theorem IsLocalHom.of_field {K S : Type*} [Field K] [CommRing S] [Nontrivial S]
    (f : K →+* S) : IsLocalHom f :=
  ⟨fun a ha ↦ by
    rcases eq_or_ne a 0 with rfl | h
    · rw [map_zero] at ha
      exact absurd (isUnit_zero_iff.mp ha) (zero_ne_one (α := S))
    · exact isUnit_iff_ne_zero.mpr h⟩
