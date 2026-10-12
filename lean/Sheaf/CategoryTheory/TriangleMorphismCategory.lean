/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Limits.Final
import Sheaf.CategoryTheory.TriangleCommonRefinement
import Sheaf.CategoryTheory.Triangulated.DenominatorTriangleCompletion

/-! # Incoming morphisms of distinguished triangles

Source: Stacks Project, Derived Categories, Tag 05R9, dual cofiltered form
(blueprint: lem-pur-triangle-morphism-category-05r9).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- Incoming morphisms of distinguished triangles with all components in `S` form a
cofiltered category, and each vertex projection to the denominator category is initial.
Source: Stacks Project, Derived Categories, Tag 05R9, dual cofiltered form
(blueprint: lem-pur-triangle-morphism-category-05r9).

Proof:
1. Complete any prescribed denominator at a vertex to a morphism of distinguished triangles
   using `lem-pur-triangle-completion-ms6-05r9`. This supplies the existence part of initiality.
2. The identity triangle morphism gives an object by MS1. Common refinements and equalizers
   from `lem-pur-triangle-common-refinement-ms3-05r9` give cofilteredness.
3. For two objects over the same denominator, take a common refinement. MS3 equalizes the
   two induced vertex maps after a further denominator. Complete that denominator to a
   triangle morphism using `lem-pur-triangle-completion-ms6-05r9` and compose by MS1. This
   supplies a connecting span in the costructured arrow category, hence initiality at the
   first vertex. Rotate triangles by TR2 and use MS5 to obtain the other two vertices.

The category is built directly from Mathlib's restricted over-category and full subcategory.
`W` requires all three components to lie in `S`, both for objects and for arrows. The full
subcategory `P` requires the source triangle to be distinguished. The targets `S.Over ⊤ _`
allow every commuting triangle as a morphism, as in Stacks Tag 05Q4. -/
theorem triangle_morphism_category_cofiltered_initial
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : MorphismProperty C) (hS : S.IsSaturatedMultiplicativeSystem)
    [S.IsCompatibleWithTriangulation] (T : Triangle C) (_hT : T ∈ distTriang C) :
    letI : S.HasLeftCalculusOfFractions := hS.1.1
    let W : MorphismProperty (Triangle C) :=
      S.inverseImage Triangle.π₁ ⊓ (S.inverseImage Triangle.π₂ ⊓ S.inverseImage Triangle.π₃)
    let P : ObjectProperty (W.Over W T) := fun x ↦ x.left ∈ distTriang C
    let p₁ : P.FullSubcategory ⥤ S.Over ⊤ T.obj₁ := {
      obj := fun x ↦ MorphismProperty.Over.mk ⊤ x.obj.hom.hom₁ x.obj.prop.1
      map := fun f ↦ MorphismProperty.Over.homMk f.hom.left.hom₁
        (Triangle.π₁.congr_map (MorphismProperty.Over.w f.hom))
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
    let p₂ : P.FullSubcategory ⥤ S.Over ⊤ T.obj₂ := {
      obj := fun x ↦ MorphismProperty.Over.mk ⊤ x.obj.hom.hom₂ x.obj.prop.2.1
      map := fun f ↦ MorphismProperty.Over.homMk f.hom.left.hom₂
        (Triangle.π₂.congr_map (MorphismProperty.Over.w f.hom))
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
    let p₃ : P.FullSubcategory ⥤ S.Over ⊤ T.obj₃ := {
      obj := fun x ↦ MorphismProperty.Over.mk ⊤ x.obj.hom.hom₃ x.obj.prop.2.2
      map := fun f ↦ MorphismProperty.Over.homMk f.hom.left.hom₃
        (Triangle.π₃.congr_map (MorphismProperty.Over.w f.hom))
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
    IsCofiltered P.FullSubcategory ∧ p₁.Initial ∧ p₂.Initial ∧ p₃.Initial := by
  sorry

end CategoryTheory
