/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular systems of parameters

Source: Stacks Project, Definition 00KU
(blueprint: def-weil-pbc-regular-system-of-parameters).
-/

universe w

namespace IsLocalRing

/-- A regular system of parameters is an ordered list of generators of the maximal ideal,
with length equal to the Krull dimension. Source: Stacks, Definition 00KU
(blueprint: def-weil-pbc-regular-system-of-parameters). The empty list is allowed in dimension zero.
-/
def IsRegularSystemOfParameters {R : Type w} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (t : List R) : Prop :=
  Ideal.span {x | x ∈ t} = maximalIdeal R ∧ (t.length : WithBot ℕ∞) = ringKrullDim R

end IsLocalRing
