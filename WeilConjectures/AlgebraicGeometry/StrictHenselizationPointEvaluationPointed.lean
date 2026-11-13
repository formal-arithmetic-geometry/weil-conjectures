/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation

/-! # Pointedness of colimit evaluation

## References

* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

-- The colimit comparison unfolds the full affine neighborhood diagram.
/-- Evaluation recovers the given geometric point at every chosen neighbourhood.
 This is the colimit coprojection equation,
followed by the naturality and triangle identities of Γ and Spec.. -/
theorem strictHenselizationPointEvaluation_pointed
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{v} (strictHenselizationNeighbourhoods barY)) :
    Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barY)) ≫
      (strictHenselizationAffineCone barY).π.app (op (op j)) ≫
      (Spec (unop ((equivSmallModel.{v}
        (strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)).isoSpec.inv =
      ((equivSmallModel.{v} (strictHenselizationNeighbourhoods barY)).inverse.obj
        j).2.left := by
  let V := Spec (unop ((equivSmallModel.{v}
    (strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)
  let z : Spec (.of Ω) ⟶ V :=
    ((equivSmallModel.{v} (strictHenselizationNeighbourhoods barY)).inverse.obj j).2.left
  change Spec.map ((isColimitSmallStrictHenselizationCocone barY).desc
      (strictHenselizationPointCocone barY)) ≫
    Spec.map ((smallStrictHenselizationCocone barY).ι.app (op j)) ≫ V.isoSpec.inv = z
  rw [← Spec.map_comp_assoc, (isColimitSmallStrictHenselizationCocone barY).fac]
  change Spec.map (z.appTop ≫ (ΓSpecIso (.of Ω)).hom) ≫ V.isoSpec.inv = z
  rw [Spec.map_comp, SpecMap_ΓSpecIso_hom, ← toSpecΓ_naturality]
  change z ≫ V.isoSpec.hom ≫ V.isoSpec.inv = z
  simp

end AlgebraicGeometry.Scheme
