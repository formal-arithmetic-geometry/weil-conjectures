/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.ProperFaceMatchingObject
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-! # Étale hypercovers over algebraic spaces and scheme base change

Source: Stacks Project, Hypercoverings, Tags 0DAY and 0DB2; Spaces, Tag 025Y
(blueprint: def-sfb-space-etale-hypercover).

A space over a scheme T is already a sheaf on Sch/T. Its product there with h_V
is the fibre product X ×_T V. The matching condition is tested in the slice of
fppf sheaves over X, including the empty boundary in degree zero.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pull a scheme over T back to X. This is the actual product of X with its
representable sheaf on Sch/T, with the first projection as structure map.
Source: Stacks, Tags 02X2 and 0DAY (blueprint: def-sfb-space-etale-hypercover). -/
def schemeBaseChange {T : Scheme.{u}} (X : AlgebraicSpace T) :
    Over T ⥤ Over X.obj where
  obj V := Over.mk (prod.fst : X.obj ⨯ (Scheme.fppfTopology.over T).yoneda.obj V ⟶ X.obj)
  map f := Over.homMk
    (prod.map (𝟙 X.obj) ((Scheme.fppfTopology.over T).yoneda.map f)) (by simp)
  map_id V := by
    apply Over.OverMorphism.ext
    simp
  map_comp f g := by
    apply Over.OverMorphism.ext
    change prod.map (𝟙 X.obj) ((Scheme.fppfTopology.over T).yoneda.map (f ≫ g)) =
      prod.map (𝟙 X.obj) ((Scheme.fppfTopology.over T).yoneda.map f) ≫
        prod.map (𝟙 X.obj) ((Scheme.fppfTopology.over T).yoneda.map g)
    rw [Functor.map_comp, prod.map_map, Category.id_comp]

/-- The all-degree étale hypercover condition for algebraic-space terms over X.
The canonical boundary cone consists of the proper-face simplicial operators;
its universal property is taken in the slice category of fppf sheaves.
In degree zero the empty matching diagram has limit X. Every term and matching
arrow is representable étale over its target; matching arrows are surjective.
Source: Stacks, Tags 025Y, 0DAY and 0186
(blueprint: def-sfb-space-etale-hypercover). -/
def IsSpaceEtaleHypercover {T : Scheme.{u}} (X : AlgebraicSpace T)
    (U : SimplicialObject (Over X.obj)) : Prop :=
  (∀ n : ℕ, IsAlgebraicSpace (U.obj (op (SimplexCategory.mk n))).left ∧
    IsEtale (U.obj (op (SimplexCategory.mk n))).hom.hom) ∧
  ∀ n : ℕ, ∃ (c : Cone (U.properFaceDiagram n)) (hc : IsLimit c),
    IsEtale (hc.lift (U.mapCone
      (((Over.forgetCocone (SimplexCategory.mk n)).whisker
        (SimplicialObject.properFaceProperty n).ι).op))).left.hom ∧
    IsSurjective (hc.lift (U.mapCone
      (((Over.forgetCocone (SimplexCategory.mk n)).whisker
        (SimplicialObject.properFaceProperty n).ι).op))).left.hom

end AlgebraicGeometry.AlgebraicSpace
