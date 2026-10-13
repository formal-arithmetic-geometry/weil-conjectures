/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MixedAffineSectionsComplexUnit
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Sheaf.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-! # The source affine model and its extension unit normalization
Source: Stacks Project, Tags 06Z0, 08DW(2) and 0AA7.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wA
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- The extension counit computes the affine chart source, and intertwines Hom transposes.
Source: Stacks Project, Tags 06Z0, 08DW(2), 0AA7.
(blueprint: lem-sc-mixed-affine-extension-unit-normalization).

Proof: The ordinary affine tilde unit identifies H(F(P)) with P termwise, so this
complex is K-flat. Its left-derived extension counit is therefore invertible.
Identify the fixed mixedGlobalExtension adjunction with the derived extension
adjunction by left-adjoint uniqueness, preserving its unit. The source comparison a
is the inverse of extension applied to mixedSectionsComplexUnit, followed by this
counit. The affine sections comparison is invertible by the affine chart sections
unit theorem. Apply derivedη_fac_app to extension/restriction, inserting the exact
restriction comparison and quotient-to-homotopy factors. This proves the formula for
the unit. Postcompose with an arbitrary complex map f and use naturality of the
exact restriction comparison to obtain the displayed equality. It is uniform in Z
and f and uses no pullback, Leray comparison, or ordinary comparison c. Zero rings,
zero complexes and zero morphisms satisfy the same unit and naturality equations. -/
theorem exists_mixedAffineSections_extension_unit_normalization
    {S T : Scheme.{u}} [IsAffine S] (g : T ⟶ S) :
    let F : ModuleCat.{u} Γ(S, ⊤) ⥤
        SheafOfModules.{u} (moduleRings S.toRingedSpace) :=
      tilde.functor Γ(S, ⊤) ⋙ Scheme.Modules.restrictFunctor S.toSpecΓ
    let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
    let E := ModuleCat.extendScalars.{u, u, u} g.appTop.hom
    let R := ModuleCat.restrictScalars.{u} g.appTop.hom
    ∀ [F.Additive] [H.Additive] [E.Additive]
      (P : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ)
      (_hP : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(S, ⊤)) (.up ℤ)).kFlat P),
    let C := (F.mapHomologicalComplex (.up ℤ)).obj P
    let X := ((F ⋙ H).mapHomologicalComplex (.up ℤ)).obj P
    ∃ a : (mixedGlobalExtension g).obj
        ((schemeDerivedGlobalSections S).obj (DerivedCategory.Q.obj C)) ≅
      DerivedCategory.Q.obj (((F ⋙ H ⋙ E).mapHomologicalComplex (.up ℤ)).obj P),
    ∀ (Z : CochainComplex (ModuleCat.{u} Γ(T, ⊤)) ℤ)
      (f : ((E.mapHomologicalComplex (.up ℤ)).obj X) ⟶ Z),
      mixedSectionsComplexUnit S C ≫
          (mixedGlobalExtensionAdjunction g).homEquiv _ _
            (a.hom ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).mapHomologicalComplex
            (.up ℤ)).unit.app X ≫
              (R.mapHomologicalComplex (.up ℤ)).map f) ≫
          R.mapDerivedCategoryFactors.inv.app Z := by sorry

end AlgebraicGeometry
