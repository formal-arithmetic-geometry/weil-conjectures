/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleStalkFlatCounitModel
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Surjectivity of relatively flat single base change

Source: Stacks Project, Tag 0A1D.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical single-module base-change comparison is surjective on cohomology.

Source: Stacks Project, Tag 0A1D, specialized to E = O_Y[0] and G = M[0], and Tag 0DJ9. -/
theorem standard_flat_single_baseChange_homology_epi
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (n : ℤ) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    Epi ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings A.toRingedSpace)) n).map
        (standardSingleBaseChangeMap p M g)) := by
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  apply Scheme.Modules.epi_of_surjective_stalk
  intro a
  let := HasDerivedCategory.standard (ModuleCat.{u} (B.presheaf.stalk (g a)))
  let := HasDerivedCategory.standard (ModuleCat.{u} (A.presheaf.stalk a))
  obtain ⟨P, hb, hf, LF, ε, hLF, he⟩ :=
    exists_standardSingle_stalk_flat_counit_model p M hM g a
  obtain ⟨eL, eR, heq⟩ := he n
  have hK := CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat P hb hf
  have hc := ModuleCat.scalarExtensionCounit_isIso_of_kFlat
    (g.stalkMap a).hom P hK LF ε hLF
  have hiso : IsIso ((RingedSpace.moduleStalkFunctor A.toRingedSpace a).map
      ((DerivedCategory.homologyFunctor _ n).map (standardSingleBaseChangeMap p M g))) := by
    rw [heq]
    infer_instance
  have hs := (ModuleCat.epi_iff_surjective _).mp
    (show Epi ((RingedSpace.moduleStalkFunctor A.toRingedSpace a).map
      ((DerivedCategory.homologyFunctor _ n).map (standardSingleBaseChangeMap p M g))) from
        inferInstance)
  exact hs

end AlgebraicGeometry
