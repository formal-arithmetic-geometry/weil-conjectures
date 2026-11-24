/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure

/-! # Naturality of the shared derived tensor symmetry

## References

* Stacks Project, Tag 0FPB
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry

private theorem naturalDerivedSymmetry {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [BraidedCategory C] (F : C ⥤ D) (W : MorphismProperty C)
    [F.IsLocalization W] [W.ContainsIdentities] [F.HasDerivedMonoidalCategory W] :
    ∃ s : ∀ K L : DerivedMonoidal F W, K ⊗ L ≅ L ⊗ K,
      ∀ (K K' L L' : DerivedMonoidal F W) (a : K ⟶ K') (b : L ⟶ L'),
        (a ⊗ₘ b) ≫ (s K' L').hom = (s K L).hom ≫ (b ⊗ₘ a) := by
  refine ⟨DerivedMonoidal.braiding' F W, ?_⟩
  intro K K' L L' a b
  rw [tensorHom_def, Category.assoc,
    DerivedMonoidal.braiding_naturality_right,
    ← Category.assoc, DerivedMonoidal.braiding_naturality_left,
    Category.assoc, ← tensorHom_def']

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The shared derived tensor has a natural symmetry (Stacks, Tags 0FPB and 064K). -/
theorem exists_schemeDerivedTensorSymmetry (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    ∃ s : ∀ K L : schemeDerivedCategory X, K ⊗ L ≅ L ⊗ K,
      ∀ (K K' L L' : schemeDerivedCategory X) (a : K ⟶ K') (b : L ⟶ L'),
        (a ⊗ₘ b) ≫ (s K' L').hom = (s K L).hom ≫ (b ⊗ₘ a) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, u, u} _
  have := schemeModule_hasFunctorialFlatResolution X
  have := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  exact naturalDerivedSymmetry
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))

end AlgebraicGeometry
