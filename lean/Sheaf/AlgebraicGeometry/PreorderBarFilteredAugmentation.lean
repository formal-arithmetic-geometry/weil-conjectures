/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module
public import Sheaf.AlgebraicGeometry.PreorderBarLowerIdeals
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-! # Exact colimits preserve the preorder bar augmentation

Explicit constructions and proved properties for the bar-union argument.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.PreorderBar
variable {I : Type u} [Preorder I] {A : Type w} [Category.{v} A] [Abelian A]
  [HasCoproducts.{u} A] [HasCoproducts.{0} A]
  [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
  (D : I ⥤ CochainComplex A ℤ)

/-- Exact colimits preserve the preorder bar augmentation.

Source: the source-bar and finite-cone-block argument in
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-preorder-bar-filtered-augmentation).

Proof: The lower-ideal bars have colimit the full bar, and their augmentations have colimit the
supplied
colimit cocone on D. Each lower-ideal augmentation is a homotopy equivalence because that lower
ideal has greatest object j. Exact colimits preserve quasi-isomorphisms: apply
MorphismProperty.colimitsOfShape_le for HomologicalComplex.quasiIso, as proved in the source-
library GrothendieckAxioms.Colim module. Naturality of augmentation identifies the resulting
colimit map with the canonical total augmentation. -/
theorem augmentation_quasiIso (c : Cocone D) (hc : IsColimit c) :
    QuasiIso (totalAugmentation D c) := by
  change (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (totalAugmentation D c)
  apply MorphismProperty.colimitsOfShape_le
    (W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (J := I)
  exact MorphismProperty.colimitsOfShape.mk' (lowerBars D) D (lowerBarsCocone D) c
    (lowerBarsIsColimit D) hc (lowerAugmentationNat D)
    (fun j ↦ terminalAugmentation_quasiIso (lowerDiagram D j)
      ⟨j, le_rfl⟩ (fun i ↦ i.2)) (totalAugmentation D c) (lowerToFull_augmentation D c)

end CategoryTheory.PreorderBar
