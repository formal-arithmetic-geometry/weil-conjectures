/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel

import WeilConjectures.AlgebraicGeometry.AffineOpenSupportedModelExists
import WeilConjectures.AlgebraicGeometry.AffineOpenSupportedModelTorsion

/-! # Supported target models on affine opens

Source: Stacks Project, Tags 06Z0, 08EB and 08EJ.
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- A supported quasi-coherent target has a power-torsion affine module preimage.
Source: Stacks Project, Tag 08EJ, affine paragraph, and Tag 06Z0. -/
theorem affine_open_supported_target_model
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (f : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E' : schemeDerivedQCohCategory X)
    (hSupport : ∀ (i : ℤ) (x : X), x ∉ X.zeroLocus (U := ⊤) {f.val (op ⊤)} →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E'.obj).val.presheaf x)))
    (U : X.Opens) (hU : IsAffineOpen U) (k : ℤ) :
    let A := ↑(X.sheaf.obj.obj (op U))
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
      HasDerivedCategory.standard (ModuleCat.{u} A)
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    ∀ (F : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))),
      Nonempty (DerivedCategory.Q ⋙ F ≅
        (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q) →
      ∃ M : DerivedCategory (ModuleCat.{u} A),
        (∀ (i : ℤ) (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M),
          ∃ n : ℕ, (f.val (op U)) ^ n • m = 0) ∧
        Nonempty (F.obj M ≅ R.obj (E'.obj⟦k⟧)) := by
  dsimp
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} (X.sheaf.obj.obj (op U))) :=
    HasDerivedCategory.standard _
  intro F hF
  obtain ⟨M, hM⟩ := affine_open_supported_model_exists X E' U hU k F hF
  have htor := affine_open_supported_model_torsion X f E' hSupport U hU k F hF M hM
  exact ⟨M, htor, hM⟩

end AlgebraicGeometry.Scheme
