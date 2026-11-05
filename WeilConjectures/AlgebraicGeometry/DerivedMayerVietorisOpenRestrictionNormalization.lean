/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # Restriction normalization by derived units

Source: Stacks Project, Cohomology, Tags 08FE and 08BV.
(blueprint: lem-pc-derived-mayer-vietoris-open-restriction-normalization).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

section

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {C : Type u₁} {D : Type u₂} {A : Type u₃} {B : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} A] [Category.{v₄} B]
  [Abelian C] [Abelian D] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  [HasDerivedCategory.{w₃} A] [HasDerivedCategory.{w₄} B]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  [Abelian.HasKInjectiveResolutions A]
  (F : C ⥤ D) (G : A ⥤ B) (LX : C ⥤ A) (LY : D ⥤ B)
  [F.Additive] [G.Additive] [LX.Additive] [LY.Additive]
  [PreservesFiniteLimits LX] [PreservesFiniteColimits LX]
  [PreservesFiniteLimits LY] [PreservesFiniteColimits LY]
  [LX.PreservesKInjectiveComplexes]
  (e : F ⋙ LY ≅ LX ⋙ G)
  (K : HomotopyCategory C (ComplexShape.up ℤ))

end

variable (X Y : Scheme.{u}) (h : X ⟶ Y)
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ T : X.Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
  [∀ T : Y.Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
  (U : Y.Opens)

attribute [local instance 2000] schemeMVModuleAbelian

end AlgebraicGeometry
