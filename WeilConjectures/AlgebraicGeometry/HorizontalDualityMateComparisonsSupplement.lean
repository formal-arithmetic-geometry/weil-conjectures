/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DualityEquationBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.HorizontalDualityMateComparisons

/-! # Fixed endpoint comparisons for horizontal duality mates

Source: Stacks Project, Tags 0D5S, 0D5T and 0ATR.
(blueprint: lem-sc-horizontal-duality-mate-comparisons).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

noncomputable section
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Lift an ambient isomorphism between restricted functors. -/
def horizontalMateLiftIso {A : Type*} [Category A] {X : Scheme.{u}}
    {F G : A ⥤ schemeDerivedQCohCategory X}
    (i : F ⋙ (schemeDerivedQCohProperty X).ι ≅ G ⋙ (schemeDerivedQCohProperty X).ι) :
    F ≅ G :=
  NatIso.ofComponents (fun K ↦
    (schemeDerivedQCohProperty X).fullyFaithfulι.preimageIso (i.app K)) (by
      intro K L φ
      apply (schemeDerivedQCohProperty X).fullyFaithfulι.map_injective
      simpa using i.hom.naturality φ)

end
end AlgebraicGeometry
