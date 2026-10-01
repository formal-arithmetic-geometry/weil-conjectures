/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular local rings are domains

## Main results

- `IsRegularLocalRing.isDomain`: a regular local ring is an integral domain.

## Blueprint

- `sk-i-geometry`: regular local rings are domains.
-/

@[expose] public section

/-- A regular local ring is an integral domain. (blueprint: `sk-i-geometry`) -/
instance IsRegularLocalRing.isDomain (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R := by
  sorry
