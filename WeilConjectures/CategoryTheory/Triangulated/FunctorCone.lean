/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Lifting a distinguished triangle along a triangulated functor

Let `F : C ⥤ D` be a functor between pretriangulated categories which is isomorphic to a
triangulated functor, and let `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧` be a distinguished triangle in `D`. If
`T₃ ≅ F X₃`, `T₁⟦1⟧ ≅ F (X₁⟦1⟧)` and the connecting morphism `T₃ ⟶ T₁⟦1⟧` is, up to these
isomorphisms, `F δ` for some `δ : X₃ ⟶ X₁⟦1⟧`, then the cone `X₂` of `δ⟦-1⟧` satisfies
`F X₂ ≅ T₂` (`CategoryTheory.Functor.exists_distinguished_iso_obj₂_of_iso`), by TR3 and the
five lemma for triangles.

Auxiliary: `CategoryTheory.Functor.commShiftObjIsoOfIso` transports the commutation with shifts
along an isomorphism of functors.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Category Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

end CategoryTheory.Functor
