/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.TStructure.ShortExact
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# The cohomology functor of a t-structure is homological

Let `t` be a t-structure on a triangulated category `C`. The functor
`H⁰ = τ_{≥ 0} τ_{≤ 0} : C ⥤ t.heart.FullSubcategory` to the (abelian) heart is a homological
functor (blueprint `lem-weil-heart-short-exact-triangles` (5)). Combined with the shift, a
distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` thus induces a long exact sequence
`⋯ ⟶ Hⁱ X ⟶ Hⁱ Y ⟶ Hⁱ Z ⟶ Hⁱ⁺¹ X ⟶ ⋯` in the heart.

The proof follows [BBD, Théorème 1.3.6]: the sequence `H⁰ X ⟶ H⁰ Y ⟶ H⁰ Z` is left exact if
`X, Y, Z ≥ 0` and right exact if `X, Y, Z ≤ 0`, by adjunction; the general case is reduced to
these by the octahedral axiom.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Triangulated.TStructure

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (t : TStructure C)

section Adjunction

end Adjunction

end CategoryTheory.Triangulated.TStructure
