/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module
public import Sheaf.AlgebraicGeometry.PreorderBarConeDiagram
import Sheaf.AlgebraicGeometry.PreorderBarTotalConeIso

/-! # Homotopy-invertible bar augmentations give an invertible cone augmentation

Explicit constructions and proved properties for the bar-union argument.
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.PreorderBar
variable {I : Type u} [Preorder I] {A : Type w} [Category.{v} A] [Preadditive A]
  [HasZeroObject A] [HasBinaryBiproducts A] [HasCoproducts.{u} A] [HasCoproducts.{0} A]
  {D E : I ⥤ CochainComplex A ℤ} (φ : D ⟶ E)

/-- Bar totalization carries a comparison of augmented arrows to a homotopy isomorphism
on their objectwise mapping cones.

Source: the finite cone-block comparison paragraph of
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-preorder-bar-cone-augmentation).

Proof: Totalization commutes with the objectwise mapping cone. On the summand in
horizontal degree p, its comparison sends the cone's source component with the
sign (-1)^p and its target component with sign +1. This makes the horizontal
cone differential acquire the required minus sign on the source; the vertical
cone differential has the same diagonal signs and off-diagonal map on both sides.
The inverse uses the same signs. Coproduct extensionality and the two cone
inclusions prove that these chain maps are mutually inverse. The comparison
identifies the canonical cone-bar augmentation with the map between the cones
of the two bar augmentations. Those augmentations are homotopy equivalences by
hypothesis. Apply the mapping-cone triangle in the homotopy category and the
two-out-of-three theorem for a morphism of distinguished triangles. The cone
comparison is an isomorphism, so the displayed canonical augmentation is an
isomorphism as well. All maps use finite sums on each generator; no boundedness
assumption is needed. -/
theorem coneAugmentation_isIso (c : Cocone D) (e : Cocone E) (f : c.pt ⟶ e.pt)
    (hf : ∀ i, φ.app i ≫ e.ι.app i = c.ι.app i ≫ f)
    (hc : IsIso ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      (totalAugmentation D c)))
    (he : IsIso ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      (totalAugmentation E e))) :
    IsIso ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      (totalAugmentation (coneDiagram φ) (coneCocone φ c e f hf))) := by
  let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let comm := totalArrow_augmentation φ c e f hf
  let ψ := Q.mapTriangle.map (CochainComplex.mappingCone.triangleMap
    (totalArrow φ) f (totalAugmentation D c) (totalAugmentation E e) comm)
  have hg : IsIso (Q.map (CochainComplex.mappingCone.map (totalArrow φ) f
      (totalAugmentation D c) (totalAugmentation E e) comm)) :=
    Pretriangulated.isIso₃_of_isIso₁₂ ψ
      (HomotopyCategory.mappingCone_triangleh_distinguished _)
      (HomotopyCategory.mappingCone_triangleh_distinguished _) hc he
  rw [← totalConeIso_augmentation φ c e f hf, Q.map_comp]
  infer_instance

end CategoryTheory.PreorderBar
