/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

/-! # Completing denominators to morphisms of distinguished triangles

Source: Stacks Project, Derived Categories, Tag 05R9 (lemma-limit-triangles),
construction over a prescribed denominator, in its incoming-arrow form
(blueprint: lem-pur-triangle-completion-ms6-05r9).
-/

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- Every denominator into any vertex of a distinguished triangle extends to a morphism
from a distinguished triangle whose other two components are also denominators.
Source: Stacks Project, Derived Categories, Tag 05R9 (lemma-limit-triangles),
construction over a prescribed denominator, dualized to incoming arrows
(blueprint: lem-pur-triangle-completion-ms6-05r9).

Proof:
1. For `s : X' ⟶ T.obj₁`, TR1 of `def-weil-triangulated-category` gives a distinguished
   cone triangle on `s ≫ T.mor₁`, with second vertex `T.obj₂`.
2. The square with components `s` and the identity commutes. TR3 completes it to a
   triangle morphism. More precisely, choose the completion in the multiplicative system
   using MS6 of `def-pur-saturated-triangulated-localization`; MS1 puts the identity in
   the system. This gives the required first-vertex completion.
3. For the second and third vertices, rotate the triangle by TR2, apply the first-vertex
   construction, and rotate the resulting triangle morphism back. MS5 ensures membership
   in the system for all shifted components. The shift equivalences identify the prescribed
   vertex with the original object and the prescribed component with the original arrow.
-/
theorem denominator_triangle_completion
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : MorphismProperty C) (hS : S.IsSaturatedMultiplicativeSystem)
    [S.IsCompatibleWithTriangulation] (T : Triangle C) (hT : T ∈ distTriang C) :
    (∀ (X' : C) (s : X' ⟶ T.obj₁), S s →
      ∃ (Y' Z' : C) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (h' : Z' ⟶ X'⟦(1 : ℤ)⟧),
        Triangle.mk f' g' h' ∈ distTriang C ∧
          ∃ φ : Triangle.mk f' g' h' ⟶ T,
            φ.hom₁ = s ∧ S φ.hom₂ ∧ S φ.hom₃) ∧
    (∀ (Y' : C) (s : Y' ⟶ T.obj₂), S s →
      ∃ (X' Z' : C) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (h' : Z' ⟶ X'⟦(1 : ℤ)⟧),
        Triangle.mk f' g' h' ∈ distTriang C ∧
          ∃ φ : Triangle.mk f' g' h' ⟶ T,
            φ.hom₂ = s ∧ S φ.hom₁ ∧ S φ.hom₃) ∧
    (∀ (Z' : C) (s : Z' ⟶ T.obj₃), S s →
      ∃ (X' Y' : C) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (h' : Z' ⟶ X'⟦(1 : ℤ)⟧),
        Triangle.mk f' g' h' ∈ distTriang C ∧
          ∃ φ : Triangle.mk f' g' h' ⟶ T,
            φ.hom₃ = s ∧ S φ.hom₁ ∧ S φ.hom₂) := by
  sorry

end CategoryTheory
