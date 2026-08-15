/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.Additive

/-!
# The adjunction induced on categories of homological complexes

An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c` between the induced functors on
categories of homological complexes (`CategoryTheory.Adjunction.mapHomologicalComplex`),
with unit and counit given degreewise by the unit and counit of `adj`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] {ι : Type*} (c : ComplexShape ι)

/-- An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c` between the induced functors on
categories of homological complexes. -/
noncomputable def Adjunction.mapHomologicalComplex {G : D ⥤ C} {F : C ⥤ D} (adj : G ⊣ F)
    [G.Additive] [F.Additive] :
    G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c where
  unit :=
    { app := fun M =>
        { f := fun n => adj.unit.app (M.X n)
          comm' := fun i j _ => (adj.unit.naturality (M.d i j)).symm }
      naturality := fun M N φ => by
        ext n
        exact adj.unit.naturality (φ.f n) }
  counit :=
    { app := fun K =>
        { f := fun n => adj.counit.app (K.X n)
          comm' := fun i j _ => (adj.counit.naturality (K.d i j)).symm }
      naturality := fun K L ψ => by
        ext n
        exact adj.counit.naturality (ψ.f n) }
  left_triangle_components X := by
    ext n
    exact adj.left_triangle_components (X.X n)
  right_triangle_components Y := by
    ext n
    exact adj.right_triangle_components (Y.X n)

end CategoryTheory
