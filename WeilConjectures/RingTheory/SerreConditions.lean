/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Height

/-!
# Serre's conditions for Noetherian rings

## Main definitions

- `Ring.IsSerreR`: regularity in codimension at most `k`.
- `Ring.IsSerreS`: depth at least the minimum of `k` and local dimension.

## References

* [Stacks, Tag 031P], parts (1) and (2)
* [Stacks, Tag 00KF] (height as local dimension)
-/

@[expose] public section

universe u

namespace Ring

/-- Serre's condition `(R_k)` for a Noetherian ring: the localization at every prime of
height at most `k` is a regular local ring. -/
def IsSerreR (R : Type u) [CommRing R] [IsNoetherianRing R] (k : ℕ) : Prop :=
  ∀ (p : Ideal R) [p.IsPrime], p.height ≤ (k : ℕ∞) →
    IsRegularLocalRing (Localization.AtPrime p)

/-- Serre's condition `(S_k)` for a Noetherian ring: for every prime `p`, the depth of the
local ring at `p` (as a module over itself) is at least `min k (height p)`. -/
def IsSerreS (R : Type u) [CommRing R] [IsNoetherianRing R] (k : ℕ) : Prop :=
  ∀ (p : Ideal R) [p.IsPrime],
    min (k : ℕ∞) p.height ≤
      IsLocalRing.depth (R := Localization.AtPrime p) (Localization.AtPrime p)

end Ring
