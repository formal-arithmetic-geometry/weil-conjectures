/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.QCohAcyclicDerivedSectionsComparison
import WeilConjectures.AlgebraicGeometry.ModuleSheafificationAffineRestriction

/-! # Cohomology of acyclic quasi-coherent derived pushforward

## References

* Stacks Project, Tags 08D4, 08D5 and 0AVW.
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- If higher direct images vanish on quasi-coherent modules, cohomology of unbounded
derived pushforward is naturally isomorphic to direct image of cohomology
(Stacks, Tags 08D4, 08D5 and 0AVW). -/
theorem qcoh_acyclic_derived_pushforward_cohomology {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hacyc : ∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      F.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
        IsZero ((schemeModuleHigherDirectImage f p).obj F))
    (i : ℤ) :
    Nonempty ((schemeDerivedQCohProperty X).ι ⋙ schemeHigherDirectImage f i ≅
      (schemeDerivedQCohProperty X).ι ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i ⋙
        RingedSpace.moduleDirectImage f.toLRSHom.toShHom) := by
  obtain ⟨⟨sectionsIso⟩, ⟨pushforwardIso⟩⟩ :=
    qcoh_acyclic_derived_sections_comparison f hacyc i
  obtain ⟨sheafIso⟩ := module_sheafification_iso_of_affine_restriction Y
    ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedSectionPresheaf f i)
    ((schemeDerivedQCohProperty X).ι ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i ⋙
      RingedSpace.moduleDirectImage f.toLRSHom.toShHom) sectionsIso
  exact ⟨pushforwardIso.symm ≪≫ sheafIso⟩

end AlgebraicGeometry
