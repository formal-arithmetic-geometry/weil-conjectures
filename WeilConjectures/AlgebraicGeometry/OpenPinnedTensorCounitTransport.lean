/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenPinnedTargetCounitTriangle
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSourceCounitTriangle
import WeilConjectures.AlgebraicGeometry.OpenPinnedTensorComparisonCoherence

/-! # Counit comparison for one open leg
Source: Stacks Project, Tags 08DW and 0D5S. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
private theorem transport_counit_comparison
    {I C D : Type*} [Category C] [Category D]
    (A : I → D) (B : I → C) (Q : C ⥤ D) (ε : ∀ i, A i ⟶ Q.obj (B i))
    {i j : I} (h : i = j) {E F : C}
    (a : B j ⟶ E) (b : E ⟶ F) (c : B i ⟶ F)
    (hc : a ≫ b = eqToHom (congrArg B h).symm ≫ c) :
    eqToHom (congrArg A h) ≫ ε j ≫ Q.map a ≫ Q.map b = ε i ≫ Q.map c := by
  cases h
  simp only [eqToHom_refl, Category.id_comp] at hc ⊢
  rw [← Q.map_comp, hc]

variable [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]

end AlgebraicGeometry
