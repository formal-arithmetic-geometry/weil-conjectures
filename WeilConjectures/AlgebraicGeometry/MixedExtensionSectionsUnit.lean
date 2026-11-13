/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MixedGlobalExtension
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsPullbackMate

/-! # Affine extension and sections with independent localization universes

## References

* Stacks Project, Tags 06Z0, 08DV, 08DW and 0AA7.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- On affine bases, extension of derived sections is sections of derived pullback,
with the comparison pinned by its adjunction unit. This involves only `g` and a
quasi-coherent object `Q`, with no `f` or base-change square
(Stacks, Tags 06Z0, 08DV, 08DW and 0AA7). -/
theorem exists_mixedExtensionSectionsUnit
    {Y Y' : Scheme.{u}} [IsAffine Y] [IsAffine Y'] (g : Y' ⟶ Y)
    (Q : schemeDerivedCategory Y) (hQ : schemeDerivedQCohProperty Y Q) :
    ∃ a : (mixedGlobalExtension g).obj ((schemeDerivedGlobalSections Y).obj Q) ≅
        (schemeDerivedGlobalSections Y').obj ((derivedPullback g).obj Q),
      (mixedGlobalExtensionAdjunction g).unit.app ((schemeDerivedGlobalSections Y).obj Q) ≫
          (schemeGlobalScalarRestriction g).map a.hom =
        (schemeDerivedGlobalSections Y).map ((schemeHomPullbackAdjunction g).unit.app Q) ≫
          (mixedGlobalSectionsDirectImageIso g).hom.app ((derivedPullback g).obj Q) := by
  obtain ⟨a, ha⟩ := exists_mixedAffineSectionsPullbackMate g Q hQ
  refine ⟨a, ?_⟩
  have h := ha ((derivedPullback g).obj Q) (𝟙 _)
  rw [(schemeHomPullbackAdjunction g).homEquiv_id] at h
  erw [(schemeDerivedGlobalSections Y').map_id, Category.comp_id] at h
  have h' := congrArg ((mixedGlobalExtensionAdjunction g).homEquiv _ _) h
  rw [Equiv.apply_symm_apply, (mixedGlobalExtensionAdjunction g).homEquiv_unit] at h'
  exact h'.symm

end AlgebraicGeometry
