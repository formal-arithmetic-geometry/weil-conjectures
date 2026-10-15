/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.NatIso

/-! # Abstract object pin for an overlap comparison

The calculation here is independent of the scheme, open-site, and transport
constructions. Source: Stacks Project, Tags 08DW and 0D5S.
-/

@[expose] public section

open CategoryTheory
namespace AlgebraicGeometry

/-- The object pin follows from the two component triangles.

Proof: Substitute the factorization of the prescribed map through gamma,
theta, and the open-site return. Functoriality turns its image into the
composite of their images. The object triangle replaces the theta-return
composite followed by the apex object and base comparisons with the middle
comparison followed by the stage object map. Associativity then lets the
natural triangle replace the gamma-middle composite by the component of the
natural comparison. This argument applies to either open and requires no
identification of the underlying dependent comparison records. -/
theorem perfectOverlapObjectPin_of_triangles
    {C D E F : Type*} [Category* C] [Category* D]
    [Category* E] [Category* F]
    (G : C ⥤ D) (apex : D ⥤ E) (stage : C ⥤ F) (transition : F ⥤ E)
    (comparison : G ⋙ apex ≅ stage ⋙ transition)
    (X : C) (O Y Z : D) (Q : F) (P : E)
    (ψ : G.obj X ≅ O) (apexObj : apex.obj O ≅ P)
    (base : P ≅ transition.obj Q) (stageObj : stage.obj X ≅ Q)
    (gamma : G.obj X ⟶ Y) (theta : Y ⟶ Z) (returnMap : Z ⟶ O)
    (middle : apex.obj Y ⟶ transition.obj (stage.obj X))
    (hψ : ψ.hom = gamma ≫ theta ≫ returnMap)
    (hnatural : apex.map gamma ≫ middle = comparison.hom.app X)
    (hobject : apex.map theta ≫ apex.map returnMap ≫ apexObj.hom ≫ base.hom =
      middle ≫ transition.map stageObj.hom) :
    apex.map ψ.hom ≫ apexObj.hom ≫ base.hom =
      comparison.hom.app X ≫ transition.map stageObj.hom := by
  calc
    apex.map ψ.hom ≫ apexObj.hom ≫ base.hom =
        apex.map gamma ≫
          (apex.map theta ≫ apex.map returnMap ≫ apexObj.hom ≫ base.hom) := by
            rw [hψ]
            simp only [Functor.map_comp, Category.assoc]
    _ = apex.map gamma ≫ (middle ≫ transition.map stageObj.hom) := by
          rw [hobject]
    _ = comparison.hom.app X ≫ transition.map stageObj.hom := by
          rw [← Category.assoc, hnatural]

/-- Pasting the site-return and pullback-comparison component triangles gives
the object pin. Source: Stacks Project, Tags 08DW and 0D5S.

Proof: The site-return equation identifies the transported theta and return
maps with a single map to the apex pullback object. The projection comparison
equation identifies that map followed by the fixed base comparison with the
stage object map after the middle comparison. These are exactly the two
component equations required by `perfectOverlapObjectPin_of_triangles`; its
conclusion follows for either open. -/
theorem perfectOverlapObjectPin_of_component_triangles
    {C D E F : Type*} [Category* C] [Category* D]
    [Category* E] [Category* F]
    (G : C ⥤ D) (apex : D ⥤ E) (stage : C ⥤ F) (transition : F ⥤ E)
    (comparison : G ⋙ apex ≅ stage ⋙ transition)
    (X : C) (O Y Z : D) (Q : F) (P : E)
    (ψ : G.obj X ≅ O) (apexObj : apex.obj O ≅ P)
    (base : P ≅ transition.obj Q) (stageObj : stage.obj X ≅ Q)
    (gamma : G.obj X ⟶ Y) (theta : Y ⟶ Z) (returnMap : Z ⟶ O)
    (middle : apex.obj Y ⟶ transition.obj (stage.obj X))
    (siteMiddle : apex.obj Y ⟶ P)
    (hψ : ψ.hom = gamma ≫ theta ≫ returnMap)
    (hnatural : apex.map gamma ≫ middle = comparison.hom.app X)
    (hreturn : apex.map theta ≫ apex.map returnMap ≫ apexObj.hom = siteMiddle)
    (hbase : siteMiddle ≫ base.hom =
      middle ≫ transition.map stageObj.hom) :
    apex.map ψ.hom ≫ apexObj.hom ≫ base.hom =
      comparison.hom.app X ≫ transition.map stageObj.hom := by
  apply perfectOverlapObjectPin_of_triangles G apex stage transition comparison
    X O Y Z Q P ψ apexObj base stageObj gamma theta returnMap middle hψ hnatural
  simp only [← Category.assoc] at hreturn ⊢
  rw [hreturn, hbase]

end AlgebraicGeometry
