/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Local ring homomorphisms with a section and square-zero kernel

A ring homomorphism `f : R →+* S` admitting a section `g` and whose kernel consists of elements of
square zero is local: an element `y` with `f y` a unit differs from the unit `g (f y)` by a
nilpotent element.
-/

@[expose] public section

/-- A ring homomorphism with a section whose kernel consists of elements of square zero is
local. -/
theorem isLocalHom_of_rightInverse_of_mul_self_eq_zero {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : S →+* R) (hg : Function.RightInverse g f)
    (hker : ∀ y, f y = 0 → y * y = 0) : IsLocalHom f where
  map_nonunit y hy := by
    have hn : IsNilpotent (y - g (f y)) :=
      ⟨2, by rw [pow_two]; exact hker _ (by simp [hg (f y)])⟩
    simpa using hn.isUnit_add_right_of_commute (hy.map g) (Commute.all _ _)
