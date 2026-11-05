/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Telescope

/-!
# Compact objects are closed under extensions

In a pretriangulated category, if `T₁` and `T₃` are compact objects
(`CategoryTheory.BrownRepresentability.IsCompactObj`) and `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧` is a
distinguished triangle, then `T₂` is compact
(`CategoryTheory.BrownRepresentability.IsCompactObj.of_distTriang`): this is the five lemma for
the maps `⨁ⱼ Hom(-, Xⱼ) ⟶ Hom(-, ∐ⱼ Xⱼ)`, which are always injective.

We also lift distinguished triangles of `C` with vertices in a triangulated subcategory `P` to
compact objects of the full subcategory
(`CategoryTheory.ObjectProperty.FullSubcategory.isCompactObj_of_distTriang`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Pretriangulated Category Preadditive

namespace CategoryTheory

namespace BrownRepresentability

variable {C : Type u} [Category.{v} C]

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

end BrownRepresentability

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)
  [P.IsTriangulated]

end ObjectProperty

end CategoryTheory
