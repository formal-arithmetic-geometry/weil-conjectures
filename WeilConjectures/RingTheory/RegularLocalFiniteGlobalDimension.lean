/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.RingTheory.GlobalDimension
import WeilConjectures.RingTheory.GlobalDimensionFiniteModules
import WeilConjectures.RingTheory.RegularLocalFiniteModuleResolution

/-!
# Global dimension of a regular local ring

A regular local ring of Krull dimension `d` has global dimension at most `d`.

## Implementation details

The generators of the maximal ideal form a regular sequence (Tag 00NQ), so the depth is at
least `d`. A nonzero finite module of depth `e` has a finite free resolution of length `d - e`
ending in a maximal Cohen–Macaulay module (Tag 00NG), which is free (Tag 00NT). Padding with
zeros gives resolutions of length at most `d` for all finite modules, and Tag 065T passes to all
modules.

## References

* [Stacks, Tag 00O7] (last assertion)
* [Stacks, Tags 00NQ, 00NG, 00NT, 065T]
-/

@[expose] public section

universe u v

namespace IsRegularLocalRing

/-- A regular local ring of Krull dimension `d` has global dimension at most `d`:
every module, without a finite generation assumption, has a projective resolution
of length at most `d`. In particular its global dimension is finite. -/
theorem hasGlobalDimensionLE_of_ringKrullDim_eq
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    Ring.HasGlobalDimensionLE.{u, max u v} R d := by
  have hfinite : ∀ M : ModuleCat.{max u v} R, Module.Finite R M →
      ModuleCat.HasProjectiveResolutionLE M d :=
    finiteModule_hasProjectiveResolutionLE R d hd
  exact (Ring.hasGlobalDimensionLE_iff_finite_iff_cyclic R d).1.mpr hfinite

end IsRegularLocalRing
