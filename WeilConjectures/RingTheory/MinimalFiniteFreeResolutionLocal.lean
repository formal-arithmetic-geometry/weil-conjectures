/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.RingTheory.BoundedFiniteFreeResolution
import WeilConjectures.RingTheory.MinimalizeBoundedFiniteFreeResolution

/-!
# Minimal finite free resolutions over a Noetherian local ring

A finite module of finite projective dimension over a Noetherian local ring has a minimal finite
free resolution of the same length.

## Implementation details

A finite projective module over a local ring is free. For `d ≥ 1`, the `d`-th syzygy of a finite
free resolution is finite projective, hence free, giving a finite free resolution of length at
most `d`. If a differential has a unit matrix entry, an identity summand `R → R` splits off;
each removal decreases the sum of the ranks, so this terminates, and then all entries lie in the
maximal ideal.

## References

* [Stacks, Tags 0CXF, 00MT] (as used in the proof of Tag 00OA)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A finite module over a Noetherian local ring with a projective resolution of length
at most `d` has a finite free resolution of length at most `d` whose positive-degree
maps have image in the maximal ideal times the preceding module. -/
theorem exists_minimal_finite_free_resolution {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{max u v} R) [Module.Finite R M]
    (d : ℕ) (h : HasProjectiveResolutionLE M d) :
    ∃ P : ProjectiveResolution M,
      (∀ i : ℕ, d < i → IsZero (P.complex.X i)) ∧
      (∀ i : ℕ, Module.Finite R (P.complex.X i) ∧ Module.Free R (P.complex.X i)) ∧
      (∀ i : ℕ, i < d →
        LinearMap.range (P.complex.d (i + 1) i).hom ≤
          IsLocalRing.maximalIdeal R • (⊤ : Submodule R (P.complex.X i))) := by
  obtain ⟨P, hzero, hfree⟩ := exists_bounded_finite_free_resolution M d h
  exact minimalize_bounded_finite_free_resolution M d P hzero hfree

end ModuleCat
