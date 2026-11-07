/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension

/-!
# The structural morphism of the strict henselization

The strict henselization `S_(s)` of a scheme `S` at a geometric point `s` maps to `S` through
every affine pointed étale neighbourhood; this module names that canonical morphism.

Source: Stacks Project, Tag 03Q9, proof
(blueprint: def-weil-pbc-strict-henselization-structural-map).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme


/-- The representative limit legs factor through upstream's structure morphism. -/
theorem strictHenselizationStructuralMap_eq
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
    (strictHenselizationAffineCone s).π.app (Opposite.op (Opposite.op j)) ≫
        Spec.map (ΓSpecIso
          (((equivSmallModel.{u}
            (strictHenselizationNeighbourhoods s)).inverse.obj j).1.left.unop)).inv ≫
        ((AffineEtale.Spec S).obj
          (((equivSmallModel.{u}
            (strictHenselizationNeighbourhoods s)).inverse.obj j).1)).hom =
      strictLocalizationToBase s := by
  let n := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j
  let x := (strictHenselizationAffineInclusion s).obj n
  have hi : Spec.map (ΓSpecIso n.1.left.unop).inv = inv x.obj.1.left.toSpecΓ := by
    apply (cancel_mono x.obj.1.left.toSpecΓ).mp
    change Spec.map (ΓSpecIso n.1.left.unop).inv ≫
      (Spec n.1.left.unop).toSpecΓ = _
    simp only [SpecMap_ΓSpecIso_inv_toSpecΓ, IsIso.inv_hom_id]
  change Spec.map (colimit.ι (strictHenselizationDiagram s) (Opposite.op x)) ≫
    Spec.map (ΓSpecIso n.1.left.unop).inv ≫ x.obj.1.hom = _
  rw [hi]
  exact strictLocalizationCone_π_app_hom s x

end AlgebraicGeometry.Scheme
