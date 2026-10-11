/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.CategoryTheory.CompactlyGenerated
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Brown representability criterion for a right adjoint

Source: Stacks Project, Derived Categories, Tag 0A8G, Proposition `proposition-brown`
(blueprint: lem-pc-brown-representability-right-adjoint).
-/

universe w u₁ u₂ v₁ v₂

open CategoryTheory.Limits

namespace CategoryTheory

/-- An exact functor from a compactly generated triangulated category that preserves
set-indexed coproducts has a right adjoint. Source: Stacks Project, Tag 0A8G,
Proposition `proposition-brown` (blueprint: lem-pc-brown-representability-right-adjoint).
The indexing universe contains both morphism universes and an arbitrary universe `w`
for the generating set; object universes are independent.

Proof: For each `d : D`, the additive functor `Hom_D(F(-), d)` is cohomological:
exactness of `F` sends distinguished triangles to distinguished triangles, whose Hom
sequences are exact. Preservation of coproducts by `F` and the universal property of
coproducts show that this functor sends coproducts to products. Apply
`lem-pc-brown-cohomological-representability` to represent it by an object `G(d)` of `C`.
For a morphism `d ⟶ d'`, Yoneda gives the unique map `G(d) ⟶ G(d')` corresponding to
postcomposition on these Hom functors. Uniqueness gives identities and composition,
and makes the representing Hom bijections natural in both variables. These bijections
give the adjunction `F ⊣ G`.
-/
theorem brownRepresentabilityRightAdjoint
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated C] [IsTriangulated D]
    [HasCoproducts.{max w v₁ v₂} C] [HasCoproducts.{max w v₁ v₂} D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hC : IsCompactlyGeneratedTriangulated.{max w v₁ v₂} C)
    (hF : ∀ I : Type (max w v₁ v₂), PreservesColimitsOfShape (Discrete I) F) :
    F.IsLeftAdjoint := by
  sorry

end CategoryTheory
