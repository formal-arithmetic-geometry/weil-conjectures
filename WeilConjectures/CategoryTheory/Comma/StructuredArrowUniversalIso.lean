/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Transport of universal arrows along isomorphisms

A universal arrow `g : X ⟶ R.obj Y` stays universal after precomposition with an isomorphism
`X' ≅ X` and postcomposition with the image of an isomorphism `Y ≅ Y'`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.StructuredArrow

variable {C : Type*} [Category C] {D : Type*} [Category D] {R : D ⥤ C}

end CategoryTheory.StructuredArrow
