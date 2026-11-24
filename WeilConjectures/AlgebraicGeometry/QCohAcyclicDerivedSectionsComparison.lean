/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedSectionPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.QCohAcyclicDerivedSectionsComparisonSections
import WeilConjectures.AlgebraicGeometry.QCohAcyclicDerivedSectionsComparisonSheafification

/-! # Derived sections for acyclic quasi-coherent pushforward

## References

* Stacks Project, Tags 08D4, 08D5, 0AVW and 0D5X.
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Derived sections over the inverse images of affine opens compute sections of
cohomology, naturally in the derived object and compatibly with restriction. The
full section cohomology presheaf sheafifies to the cohomology of derived direct image
(Stacks, Tags 08D4, 08D5, 0AVW and 0D5X). -/
theorem qcoh_acyclic_derived_sections_comparison {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hacyc : ∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      F.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
        IsZero ((schemeModuleHigherDirectImage f p).obj F))
    (i : ℤ) :
    Nonempty
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedSectionPresheaf f i ⋙
          PresheafOfModules.pushforward₀
            (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
            (moduleRings Y.toRingedSpace).obj ≅
        (schemeDerivedQCohProperty X).ι ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i ⋙
          RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
          SheafOfModules.forget (moduleRings Y.toRingedSpace) ⋙
          PresheafOfModules.pushforward₀
            (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
            (moduleRings Y.toRingedSpace).obj) ∧
    Nonempty
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedSectionPresheaf f i ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings Y.toRingedSpace).obj) ≅
        (schemeDerivedQCohProperty X).ι ⋙ schemeHigherDirectImage f i) := by
  obtain ⟨sectionsIso⟩ :=
    qcoh_acyclic_derived_sections_comparison_sections f hacyc i
  obtain ⟨sheafificationIso⟩ :=
    qcoh_acyclic_derived_sections_comparison_sheafification f hacyc i
  exact ⟨⟨sectionsIso⟩, ⟨sheafificationIso⟩⟩

end AlgebraicGeometry
