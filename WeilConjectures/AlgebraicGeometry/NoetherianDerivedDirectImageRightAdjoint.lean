/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint

/-! # A right adjoint to derived direct image for Noetherian schemes

## References

* Stacks Project, Duality for Schemes, Lemma 48.3.1 (Tag 0A9E), and Derived Categories
  of Schemes, Lemma 36.4.1 (1) (Tag 08D5).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- Derived direct image between Noetherian schemes preserves quasi-coherent cohomology,
and its restriction to the full quasi-coherent derived subcategories has a right adjoint
(Stacks, Tags 0A9E and 08D5). -/
theorem noetherian_schemeDerivedDirectImage_has_rightAdjoint
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian Y] [CompactSpace Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) :
    ∃ h : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj),
      ((schemeDerivedQCohProperty Y).lift
        ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) h).IsLeftAdjoint := by
  obtain ⟨hpres, hadj⟩ := schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f
  exact ⟨fun E ↦ hpres E.obj E.property, hadj⟩

end AlgebraicGeometry
