/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageUniformAffineTruncation

/-! # Uniform truncation of the two sides over an affine open

## References

* Stacks Project, Tags 08DZ and 08D5
-/

@[expose] public section

universe u₁ w₁ w₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Over one affine open, the two vertical maps of the coproduct comparison square
are isomorphisms for a common lower truncation. The integer may depend on that open
(Stacks, Tags 08DZ and 08D5). -/
theorem exists_derivedDirectImage_coproduct_affine_truncation
    {X Y : Scheme.{u₁}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))]
    (I : Type u₁) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (q : ℤ) (U : Y.Opens) (hU : IsAffineOpen U) :
    ∃ a : ℤ,
      IsIso ((SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op U)).map
        (Limits.Sigma.map (fun i ↦ (schemeHigherDirectImage f q).map
          ((DerivedCategory.TStructure.t.truncGEπ a).app (E i).obj)))) ∧
      IsIso ((SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op U)).map
        ((schemeHigherDirectImage f q).map
          ((DerivedCategory.TStructure.t.truncGEπ a).app S))) := by
  have : (schemeDerivedQCohProperty X).IsClosedUnderColimitsOfShape (Discrete I) :=
    schemeDerivedQCohClosedUnderCoproducts X I
  have hS : schemeDerivedQCohProperty X S :=
    (schemeDerivedQCohProperty X).prop_of_isColimit hc (fun i ↦ (E i.as).property)
  obtain ⟨a, ha⟩ :=
    exists_isIso_schemeHigherDirectImage_uniform_truncGE_over_affine f q U hU
  let R := moduleRings Y.toRingedSpace
  let r := SheafOfModules.overFunctor.{u₁} R U
  have : r.IsLeftAdjoint :=
    inferInstanceAs ((SheafOfModules.pushforward.{u₁} (𝟙 (R.over U))).IsLeftAdjoint)
  have : PreservesColimitsOfShape (Discrete I) r := inferInstance
  let A := fun i ↦ (schemeHigherDirectImage f q).obj (E i).obj
  let B := fun i ↦ (schemeHigherDirectImage f q).obj
    ((DerivedCategory.TStructure.t.truncGE a).obj (E i).obj)
  let p : ∀ i, A i ⟶ B i := fun i ↦ (schemeHigherDirectImage f q).map
    ((DerivedCategory.TStructure.t.truncGEπ a).app (E i).obj)
  have hp : ∀ i, IsIso (r.map (p i)) := fun i ↦ ha (E i)
  have hnat : sigmaComparison r A ≫ r.map (Limits.Sigma.map p) =
      Limits.Sigma.map (fun i ↦ r.map (p i)) ≫ sigmaComparison r B := by
    apply Sigma.hom_ext
    intro i
    simp only [ι_comp_sigmaComparison_assoc, Sigma.ι_map_assoc,
      ι_comp_sigmaComparison, ← r.map_comp, Sigma.ι_map]
  have hiso : IsIso (sigmaComparison r A ≫ r.map (Limits.Sigma.map p)) := by
    rw [hnat]
    infer_instance
  have hr : IsIso (r.map (Limits.Sigma.map p)) :=
    IsIso.of_isIso_comp_left (sigmaComparison r A) _
  let ev := SheafOfModules.evaluation (R.over U) (op (Over.mk (𝟙 U)))
  refine ⟨a, ?_, ?_⟩
  · change IsIso (ev.map (r.map (Limits.Sigma.map p)))
    infer_instance
  · have hs := ha ⟨S, hS⟩
    change IsIso (ev.map (r.map ((schemeHigherDirectImage f q).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app S))))
    infer_instance

end AlgebraicGeometry
