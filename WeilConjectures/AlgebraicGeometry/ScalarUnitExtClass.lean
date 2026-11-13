/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarUnitCohomologyCoordinates
import all WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonNormalization

/-! # ScalarUnitExtClass

## References

* [Stacks Project, Tag 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 01DZ](https://stacks.math.columbia.edu/tag/01DZ)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}}
attribute [local instance] Sheaf.monoidalCategory HasExt.standard

/-- The cohomology class of one corresponds to the degree-zero scalar-unit morphism. -/
theorem scalarUnitCohomologyClass_ext
    (f : X ⟶ Spec (CommRingCat.of k)) :
    scalarCohomologyExtEquiv f (SheafOfModules.unit X.ringCatSheaf) 0
      (scalarUnitCohomologyClass f) = Abelian.Ext.mk₀ (scalarUnitMorphism f) := by
  classical
  let : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
    hasExt_of_enoughInjectives.{u, u, u + 1} (SheafOfModules.{u} X.ringCatSheaf)
  let U := SheafOfModules.unit X.ringCatSheaf
  let I := injectiveResolution U
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let a := (I.toRightDerivedZero' S).hom (1 : Γ(X, ⊤))
  have ha : (I.ι.f 0).val.app (Opposite.op ⊤) (1 : Γ(X, ⊤)) =
      (RingedSpace.globalSectionsComplex I).iCycles 0 a := by
    exact (ConcreteCategory.congr_hom (I.toRightDerivedZero'_comp_iCycles S)
      (1 : Γ(X, ⊤))).symm
  have h := (Classical.choose_spec (exists_moduleExtEquiv U 0)) I a
    (I.ι.f 0) (by simp) ha
  have hclass : scalarUnitCohomologyClass f =
      (I.isoRightDerivedObj S 0).inv
        ((RingedSpace.globalSectionsComplex I).homologyπ 0 a) := by
    unfold scalarUnitCohomologyClass
    rw [I.toRightDerivedZero_eq]
    rfl
  have hm : moduleExtEquiv U 0 (scalarUnitCohomologyClass f) =
      Abelian.Ext.mk₀ (𝟙 U) := by
    unfold moduleExtEquiv
    rw [hclass, h]
    simpa using extMk_augmentation I (𝟙 U)
  unfold scalarCohomologyExtEquiv scalarCohomologyExtMap scalarExtMap
  change (Abelian.Ext.mk₀ (scalarUnitMorphism f)).comp
    ((moduleExtEquiv U 0 (scalarUnitCohomologyClass f)).mapExactFunctor
      (scalarFunctor f)) (zero_add 0) = _
  rw [hm, Abelian.Ext.mapExactFunctor_mk₀, CategoryTheory.Functor.map_id]
  change (Abelian.Ext.mk₀ (scalarUnitMorphism f)).comp
    (Abelian.Ext.mk₀ (𝟙 (scalarSheaf f U))) (add_zero 0) = _
  exact Abelian.Ext.comp_mk₀_id _

end
end AlgebraicGeometry.Scheme.Modules
