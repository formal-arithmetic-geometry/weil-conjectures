/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.Defs

/-!
# The inverse of an element of the localization submonoid
-/

@[expose] public section

/-- In `Localization S`, the fraction `1 / f` is inverse to `f / 1` for `f : S`. -/
theorem Localization.mk_one_mul_mk_one {R : Type*} [CommRing R] {S : Submonoid R} (f : S) :
    (Localization.mk 1 f : Localization S) * Localization.mk (f : R) 1 = 1 := by
  rw [Localization.mk_mul, one_mul, mul_one]
  exact Localization.mk_self f
