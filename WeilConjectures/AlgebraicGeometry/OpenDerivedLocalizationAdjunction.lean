/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.CategoryTheory.Localization.LocallySmall

/-! # Derived localizations and the adjunction for open restriction

## References

* Stacks Project, Tag 079W.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The module category of an open subscheme `U` has a derived category with Hom types in
universe `w`, transported from the localization over the open `U` of `X`. (Stacks, Tag 079W) -/
theorem nonempty_hasDerivedCategory_openSubscheme
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    Nonempty (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))) := by
  let B := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  let : HasDerivedCategory.{u + 1} D := HasDerivedCategory.standard D
  let e : B ≌ D := Scheme.Modules.overEquiv U
  let ed := e.mapDerivedCategory
  let : LocallySmall.{w} (DerivedCategory D) :=
    (locallySmall_congr ed).mp inferInstance
  exact ⟨(HomologicalComplex.quasiIso D (.up ℤ)).hasLocalizationOfLocallySmall
    DerivedCategory.Q⟩

/-- Localized restriction to an open `U` has a right adjoint on derived categories.
No support or detector assertion is made. (Stacks, Tags 079W and 0A9A) -/
theorem open_derived_localization_adjunction
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    ∃ (R : DerivedCategory
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
        schemeDerivedCategory X),
      Nonempty ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R) := by
  classical
  let B := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let : IsGrothendieckAbelian.{u} B :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
      ((Opens.grothendieckTopology X).over U) (X.toRingedSpace.sheaf.over U)).1
  let L := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let : L.IsLeftAdjoint := by dsimp [L, SheafOfModules.overFunctor]; infer_instance
  let G := Functor.rightAdjoint L
  let : G.Additive := Functor.additive_of_preserves_binary_products G
  exact ⟨G.rightDerivedFunctor,
    ⟨(Adjunction.ofIsLeftAdjoint L).mapDerivedCategoryRightDerivedAdjunction⟩⟩

end AlgebraicGeometry
