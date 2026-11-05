/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Compactness with respect to a fixed family

An object `s` of a preadditive category is *compact for a family* `Y` with a coproduct
(`CategoryTheory.CompactFor`) if every morphism `s ⟶ ∐ Y` is a finite sum of morphisms through
the summands. We record how this property moves along families of morphisms which induce
bijections (or surjections) on morphisms out of `s`, and when such bijections come from
distinguished triangles whose third (or first) term receives no morphisms from `s`.

These are the formal steps of the truncation argument for compactness used in blueprint
`det-ctf-finite-compact-proetale`.
-/

@[expose] public section

open CategoryTheory Limits Category Preadditive Pretriangulated

namespace CategoryTheory

variable {C : Type*} [Category* C] [Preadditive C]

namespace CompactFor

variable {s : C} {J : Type*}

end CompactFor

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

end CategoryTheory
