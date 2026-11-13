/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffineDerivedSectionsTruncationIso
import WeilConjectures.AlgebraicGeometry.AffineDerivedSectionsTruncatedBottom

/-! # Cohomology of derived affine sections

Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5.
-/

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- Derived affine sections commute naturally with cohomology on D_QCoh (Stacks, Tag 06Z0). -/
theorem affineDerivedSections_homology_comparison (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (G : schemeDerivedQCohCategory (Spec (.of A)) ⥤ DerivedCategory (ModuleCat.{u} A))
    (hG : Nonempty (G ≅ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        (RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor))
    (n : ℤ) :
    Nonempty (G ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ≅
      (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n ⋙
        moduleSpecΓFunctor (R := .of A)) := by
  let S := (RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  let ι := (schemeDerivedQCohProperty (Spec (.of A))).ι
  let τ := Functor.whiskerLeft ι
    (Functor.whiskerRight (Functor.whiskerRight
      (DerivedCategory.TStructure.t.truncGEπ n) S) H)
  have (K : schemeDerivedQCohCategory (Spec (.of A))) : IsIso (τ.app K) :=
    affineDerivedSections_truncGE_isIso A K n
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  obtain ⟨eG⟩ := hG
  obtain ⟨eB⟩ := affineDerivedSections_truncated_bottom A n
  exact ⟨Functor.isoWhiskerRight eG H ≪≫ asIso τ ≪≫
    Functor.isoWhiskerLeft ι eB⟩

end AlgebraicGeometry
