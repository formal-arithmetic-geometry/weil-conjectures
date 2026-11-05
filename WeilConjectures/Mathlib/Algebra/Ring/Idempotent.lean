/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Tactic.NoncommRing

/-!
# Lifting idempotents modulo a square-zero element

If `x² - x` has square zero in a ring, then `3x² - 2x³` is idempotent.
-/

@[expose] public section

