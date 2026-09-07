/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Ring.Equiv

/-!
# Currying a family of rings indexed by a product

If the family `R : κ → Type*` of rings is pulled back to `ι × κ` along the second projection,
a section of the pullback is the same thing as an `ι`-indexed family of sections of `R`.

## Main definitions

- `RingEquiv.piCurryProd`
-/

@[expose] public section

/-- Currying as a ring equivalence: if the ring `R z` attached to `z : ι × κ` only depends on
`z.2`, then a section of `R` is the same thing as an `ι`-indexed family of sections of `R`.

This is `Equiv.curry` for a family of rings indexed by the second factor. -/
def RingEquiv.piCurryProd {ι κ : Type*} (R : κ → Type*)
    [∀ k, NonUnitalNonAssocSemiring (R k)] :
    ((z : ι × κ) → R z.2) ≃+* (ι → (k : κ) → R k) where
  toFun f i k := f (i, k)
  invFun f z := f z.1 z.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
