/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular systems of parameters

A regular system of parameters of a Noetherian local ring `R` of Krull dimension `d` is a list
of `d` elements generating the maximal ideal.

## Main definitions

- `IsLocalRing.IsRegularSystemOfParameters`.
-/

@[expose] public section

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A finite list `t = (t₁, …, t_r)` of elements of a local ring `R` is a *regular system of
parameters* if its length is the Krull dimension of `R` and it generates the maximal ideal.
(blueprint: `def-weil-pbc-regular-system-of-parameters`) -/
def IsRegularSystemOfParameters (t : List R) : Prop :=
  (t.length : WithBot ℕ∞) = ringKrullDim R ∧ Ideal.span {x | x ∈ t} = maximalIdeal R

end IsLocalRing
