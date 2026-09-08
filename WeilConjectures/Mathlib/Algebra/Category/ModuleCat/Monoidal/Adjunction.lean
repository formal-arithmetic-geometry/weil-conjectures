/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# The restriction of scalars is lax braided

Let `f : R →+* S` be a morphism of commutative rings. Mathlib knows that the functor
`ModuleCat.restrictScalars f : ModuleCat S ⥤ ModuleCat R` is lax monoidal. As the
monoidal categories `ModuleCat R` and `ModuleCat S` are symmetric, we upgrade this to
a lax braided (i.e. lax symmetric monoidal) structure.

## Main declarations

* `ModuleCat.restrictScalarsLaxBraided`: `ModuleCat.restrictScalars f` is lax braided.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

open ModuleCat.MonoidalCategory in
/-- The restriction of scalars along a morphism of commutative rings is lax braided: the
structure map `μ` sends `m₁ ⊗ₜ m₂` to `m₁ ⊗ₜ m₂`, hence commutes with the symmetry which
exchanges the two factors. -/
noncomputable instance restrictScalarsLaxBraided : (restrictScalars f).LaxBraided where
  braided M N := tensor_ext fun m n ↦ by simp

end ModuleCat
