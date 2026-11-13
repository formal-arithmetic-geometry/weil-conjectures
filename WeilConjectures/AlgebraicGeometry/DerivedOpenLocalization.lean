/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.Algebra.Homology.OpenExtensionRestrictionIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.LocallySmall
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Derived localizations on opens in the ambient Hom universe

Source: Stacks Project, Tag 08BT, and Mathlib's HasDerivedCategory convention.
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- An ambient derived localization with Hom universe w supplies such localizations on
all opens. This is a size statement, not a new hypothesis on the scheme.
Source: Stacks Project, Tag 08BT (exact extension-by-zero/restriction adjunction),
and Mathlib.Algebra.Homology.DerivedCategory.Basic, HasDerivedCategory.standard. -/
theorem nonempty_derivedOpenLocalization (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    Nonempty (∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))) := by
  classical
  suffices h : ∀ U : X.Opens, Nonempty
      (HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))) from
    ⟨fun U ↦ Classical.choice (h U)⟩
  intro U
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let B := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let := HasDerivedCategory.standard B
  let E : B ⥤ A :=
    SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X.toRingedSpace) U ⋙
      PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X.toRingedSpace).obj)
  let R : A ⥤ B := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  obtain ⟨hRlim, hRcolim, hElim, hEcolim, ⟨adj⟩⟩ :=
    open_restriction_adjunction_exact X.toRingedSpace U
  let : Limits.PreservesFiniteLimits E := hElim
  let : Limits.PreservesFiniteColimits E := hEcolim
  let : Limits.PreservesFiniteLimits R := hRlim
  let : Limits.PreservesFiniteColimits R := hRcolim
  let : E.Additive := adj.left_adjoint_additive
  let : R.Additive := adj.right_adjoint_additive
  let : Limits.PreservesFiniteLimits (E ⋙ R) := Limits.comp_preservesFiniteLimits E R
  let : Limits.PreservesFiniteColimits (E ⋙ R) := Limits.comp_preservesFiniteColimits E R
  obtain ⟨e⟩ := nonempty_openExtensionRestrictionIso X.toRingedSpace U
  let d : E.mapDerivedCategory ⋙ R.mapDerivedCategory ≅ 𝟭 (DerivedCategory B) :=
    (Functor.mapDerivedCategoryCompIso E R) ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso B
  let : E.mapDerivedCategory.Faithful := Functor.Faithful.of_comp_iso d
  let : LocallySmall.{w} (DerivedCategory B) :=
    locallySmall_of_faithful E.mapDerivedCategory
  exact ⟨MorphismProperty.hasLocalizationOfLocallySmall.{w}
    (HomologicalComplex.quasiIso B (.up ℤ)) DerivedCategory.Q⟩

end AlgebraicGeometry
