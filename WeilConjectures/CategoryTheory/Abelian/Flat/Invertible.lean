/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!

# Invertible objects are flat

An object `X` of a monoidal category with a two-sided tensor inverse `Y`,
`X ⊗ Y ≅ 𝟙 ≅ Y ⊗ X`, is flat: tensoring with `X` on either side is an equivalence
(`CategoryTheory.tensorLeftEquivalence`, `CategoryTheory.tensorRightEquivalence`), and an
equivalence is exact.

## Main results

- `CategoryTheory.ObjectProperty.flat_of_tensorIso`: an object with a two-sided tensor inverse
  is flat.

-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- An object with a two-sided tensor inverse is flat: tensoring with it on either side is an
equivalence. -/
lemma flat_of_tensorIso {X Y : C} (e : X ⊗ Y ≅ 𝟙_ C) (e' : Y ⊗ X ≅ 𝟙_ C) : flat X := by
  have : (tensorLeft X).IsEquivalence := (tensorLeftEquivalence e e').isEquivalence_functor
  have : (tensorRight X).IsEquivalence := (tensorRightEquivalence e e').isEquivalence_functor
  exact ⟨⟨inferInstanceAs (PreservesFiniteLimits _), inferInstanceAs (PreservesFiniteColimits _)⟩,
    ⟨inferInstanceAs (PreservesFiniteLimits _), inferInstanceAs (PreservesFiniteColimits _)⟩⟩

end CategoryTheory.ObjectProperty
