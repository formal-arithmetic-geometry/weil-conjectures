/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module
public import Sheaf.AlgebraicGeometry.PreorderBarTotal
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # The objectwise cone diagram and augmented cocone

Explicit constructions and proved properties for the bar-union argument.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.PreorderBar
variable {I : Type u} [Preorder I] {A : Type w} [Category.{v} A] [Preadditive A]
  [HasZeroObject A] [HasBinaryBiproducts A] [HasCoproducts.{u} A] [HasCoproducts.{0} A]
  {D E : I ⥤ CochainComplex A ℤ} (φ : D ⟶ E)

/-- The objectwise cone diagram and augmented cocone.

Source: the source-bar and finite-cone-block argument in
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: def-sc-preorder-bar-cone-diagram).

Proof: At i use mappingCone(φ(i)), and on i→j use mappingCone.map for the naturality square. The
identity
and composition laws follow from mappingCone.map_id and map_comp. On the cocone use
mappingCone.map for the supplied compatible square. Cocone naturality follows from map_comp and
the two original cocone equations. -/
@[implicit_reducible]
noncomputable def coneDiagram : I ⥤ CochainComplex A ℤ where
  obj i := CochainComplex.mappingCone (φ.app i)
  map {i j} g := CochainComplex.mappingCone.map (φ.app i) (φ.app j)
    (D.map g) (E.map g) (φ.naturality g).symm
  map_id i := by simp only [Functor.map_id]; exact CochainComplex.mappingCone.map_id _
  map_comp {i j k} g h := by
    simp only [Functor.map_comp]
    exact CochainComplex.mappingCone.map_comp _ _ _ _ _ _ _ _ _

noncomputable def coneCocone (c : Cocone D) (e : Cocone E) (f : c.pt ⟶ e.pt)
    (hf : ∀ i, φ.app i ≫ e.ι.app i = c.ι.app i ≫ f) : Cocone (coneDiagram φ) where
  pt := CochainComplex.mappingCone f
  ι := { app i := CochainComplex.mappingCone.map (φ.app i) f
           (c.ι.app i) (e.ι.app i) (hf i)
         naturality {i j} g := by
           change CochainComplex.mappingCone.map (φ.app i) (φ.app j)
             (D.map g) (E.map g) (φ.naturality g).symm ≫
             CochainComplex.mappingCone.map (φ.app j) f
               (c.ι.app j) (e.ι.app j) (hf j) = _
           rw [← CochainComplex.mappingCone.map_comp]
           simp only [c.w g, e.w g, Functor.const_obj_map]
           exact (Category.comp_id _).symm }

end CategoryTheory.PreorderBar
