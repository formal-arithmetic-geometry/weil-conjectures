/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.CompactObject
public import Sheaf.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Triangulated.Yoneda
import Sheaf.CategoryTheory.CompactGeneratorsBuildObjects

/-! Detection of cohomological isomorphisms on compact generators.

Source: Stacks Project, Derived Categories, Tag 0A8F, Lemma `lemma-brown`
(blueprint: lem-pc-cohomological-generator-detection).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] [HasCoproducts.{v} C]

/-- A map from a representable cohomological functor to H is invertible everywhere
if it is invertible on every shift of the compact generators.

Source: Stacks Project, Derived Categories, Tag 0A8F, Lemma `lemma-brown`, final paragraph.
(blueprint: lem-pc-cohomological-generator-detection).

Proof: let D' consist of objects Y for which α is invertible at every shift of Y.
Naturality and the two cohomological long exact sequences give closure under
triangles by the five lemma. Shift composition gives closure under shifts, and
naturality gives closure under isomorphisms. Both functors carry coproducts to
products, so D' is closed under coproducts. Applying triangle closure to telescope
triangles gives closure under sequential homotopy colimits. The hypotheses put all
generators and their shifts in D'. The compact-generator construction of every
object from these shifts, coproducts, cones and a telescope then puts every object
in D'. At shift zero this gives the claimed invertibility. -/
theorem cohomologicalGeneratorDetection
    {I : Type v} (E : I → C) (hcompact : ∀ i : I, IsCompactObject (E i))
    (hgenerate : IsTriangulatedGeneratingFamily E)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ (J : Type v), PreservesLimitsOfShape (Discrete J) H)
    (G : C) (α : preadditiveYoneda.obj G ⟶ H)
    (hα : ∀ (i : I) (n : ℤ), IsIso (α.app (Opposite.op ((E i)⟦n⟧)))) :
    ∀ X : Cᵒᵖ, IsIso (α.app X) := by
  sorry

end CategoryTheory
