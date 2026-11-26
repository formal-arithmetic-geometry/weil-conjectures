/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular systems of parameters

## References

* [Stacks, Tag 00KU]
-/

@[expose] public section

universe w

namespace IsLocalRing

/-- A regular system of parameters is an ordered list of generators of the maximal ideal,
with length equal to the Krull dimension. The empty list is allowed in dimension zero.
-/
def IsRegularSystemOfParameters {R : Type w} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (t : List R) : Prop :=
  Ideal.span {x | x ∈ t} = maximalIdeal R ∧ (t.length : WithBot ℕ∞) = ringKrullDim R

end IsLocalRing
