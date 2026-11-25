/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageTruncatedCoproduct
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCoproductAffineTruncation
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Cohomology of a derived direct-image coproduct

## References

* Stacks Project, Tags 08DZ, 08D5
-/

@[expose] public section

universe u₁ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical direct-sum map on the cohomology sheaves of derived direct image
is an isomorphism in a fixed integer degree, where `S` is the ambient derived coproduct
(Stacks, Tags 08DZ, 08D5). -/
theorem derivedDirectImage_cohomology_coproduct
    {X Y : Scheme.{u₁}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))]
    (I : Type u₁) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (q : ℤ) :
    IsIso (Sigma.desc (fun i ↦ (schemeHigherDirectImage f q).map (ι i))) := by
  let F := schemeHigherDirectImage f q
  let c := Sigma.desc (fun i ↦ F.map (ι i))
  have hlocal (U : Y.Opens) (hU : IsAffineOpen U) :
      IsIso ((SheafOfModules.evaluation (moduleRings Y.toRingedSpace)
        (Opposite.op U)).map c) := by
    obtain ⟨a, hleft, hright⟩ :=
      exists_derivedDirectImage_coproduct_affine_truncation f I E S ι hc q U hU
    let T : schemeDerivedCategory X ⥤ schemeDerivedCategory X :=
      DerivedCategory.TStructure.t.truncGE a
    let π : 𝟭 (schemeDerivedCategory X) ⟶ T :=
      DerivedCategory.TStructure.t.truncGEπ a
    let d := Sigma.desc (fun i ↦ F.map (T.map (ι i)))
    let l := Limits.Sigma.map (fun i ↦ F.map (π.app (E i).obj))
    let r := F.map (π.app S)
    have hd : IsIso d := derivedDirectImage_truncated_cohomology_coproduct
      f I E S ι hc a q
    have square : c ≫ r = l ≫ d := by
      apply Sigma.hom_ext
      intro i
      simp only [c, l, d, r, Sigma.ι_comp_desc_assoc, Sigma.ι_map_assoc,
        Sigma.ι_comp_desc, ← F.map_comp]
      exact congrArg F.map (π.naturality (ι i))
    let ev := SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (Opposite.op U)
    have hl : IsIso (ev.map l) := hleft
    have hr : IsIso (ev.map r) := hright
    have hcomp : IsIso (ev.map c ≫ ev.map r) := by
      rw [← ev.map_comp, square, ev.map_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right (ev.map c) (ev.map r)
  have hB : TopologicalSpace.Opens.IsBasis
      (Set.range (fun U : Y.affineOpens ↦ (U : Y.Opens))) := by
    rw [Subtype.range_coe]
    exact Y.isBasis_affineOpens
  have hforget : IsIso ((SheafOfModules.toSheaf
      (moduleRings Y.toRingedSpace)).map c) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis hB
    intro U
    have : IsIso ((SheafOfModules.evaluation (moduleRings Y.toRingedSpace)
        (Opposite.op (U : Y.Opens))).map c) := hlocal U U.2
    exact inferInstanceAs (IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map
      ((SheafOfModules.evaluation (moduleRings Y.toRingedSpace)
        (Opposite.op (U : Y.Opens))).map c)))
  exact isIso_of_reflects_iso c (SheafOfModules.toSheaf (moduleRings Y.toRingedSpace))

end AlgebraicGeometry
