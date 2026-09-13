/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The underlying morphism of an isomorphism over a base

A morphism `f : Y ⟶ Z` in `Over X` is an isomorphism as soon as its underlying morphism
`f.left : Y.left ⟶ Z.left` is one and conversely, since `CategoryTheory.Over.forget X` both
preserves and reflects isomorphisms. Mathlib records the analogous instance for
`CategoryTheory.Comma`, but `Over X` carries its own category instance, so the `Comma` instance
does not apply to it.

## Main results

- `CategoryTheory.Over.isIso_left`: the underlying morphism of an isomorphism over a base is an
  isomorphism.
-/

@[expose] public section

namespace CategoryTheory.Over

variable {C : Type*} [Category* C] {X : C}

/-- The morphism underlying an isomorphism of objects over `X` is an isomorphism. -/
instance isIso_left {Y Z : Over X} (f : Y ⟶ Z) [IsIso f] : IsIso f.left :=
  inferInstanceAs (IsIso ((forget X).map f))

end CategoryTheory.Over
