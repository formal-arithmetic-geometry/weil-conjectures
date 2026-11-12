/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.ModuleCupNaiveMap
/-! # Tensor-counit normalization of the global pullback

Source: Stacks Tags 008A, 008Y, 0B6A and 0FKU. -/

@[expose] public section
universe u
set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable (X : Scheme.{u})
local instance globalSectionsLaxDataCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance globalSectionsLaxDataMonoidal :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance globalSectionsLaxDataSymmetric :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
attribute [local instance]
  instHasColimitsOfSizeSheafOfModulesOpensCarrierCarrierCommRingCatToRingedSpaceModuleRings
local instance globalSectionsLaxDataPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance globalSectionsLaxDataClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
set_option backward.isDefEq.respectTransparency true in
/-- The canonical lax structure has the concrete unit and tensor maps.
Source: Stacks, Section 17.16 (Tag 01CA), the sheaf tensor construction;
WeilConjectures.AlgebraicGeometry.Modules.TensorSection, the section tensor identities.
(blueprint: lem-sc-global-sections-lax-monoidal-data)
Proof: choose the unit map induced by unitSectionsEquiv and the tensorator induced
by the bilinear pairing tmulSection. Naturality in either argument follows by applying
whiskerRight_app_tmulSection and whiskerLeft_app_tmulSection to pure tensors.
The associativity diagram agrees on every triple of pure tensors by
associator_hom_app_tmulSection: both sides give the nested tensor section with
parentheses changed by the sheaf associator. The left and right unit diagrams agree
on pure tensors by leftUnitor_hom_app_tmulSection and rightUnitor_hom_app_tmulSection:
both sides send r tensor s (respectively s tensor r) to r times s.
TensorProduct.ext' and ModuleCat.hom_ext extend these identities to all morphisms,
so the prescribed maps define a lax monoidal structure. Its unit and tensorator
are the required maps by construction. The same equations hold for zero modules
and the empty scheme; no injectivity or surjectivity of the tensorator is asserted. -/
theorem globalSectionsFunctor_laxMonoidal_data
    :
    ∃ lax : (RingedSpace.globalSectionsFunctor X.toRingedSpace).LaxMonoidal,
      letI := lax
      Functor.LaxMonoidal.ε (RingedSpace.globalSectionsFunctor X.toRingedSpace) =
          ModuleCat.ofHom (unitSectionsEquiv (X := X) ⊤).toLinearMap ∧
      ∀ M N, Functor.LaxMonoidal.μ (RingedSpace.globalSectionsFunctor X.toRingedSpace) M N =
          moduleCup_sectionTensorMap X M N := by
  refine ⟨{
    ε := ModuleCat.ofHom (unitSectionsEquiv (X := X) ⊤).toLinearMap
    μ := moduleCup_sectionTensorMap X
    μ_natural_left := ?_
    μ_natural_right := ?_
    associativity := ?_
    left_unitality := ?_
    right_unitality := ?_ }, rfl, fun _ _ ↦ rfl⟩
  · intro M N f P
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.MonoidalCategory.associator_hom_apply,
      ModuleCat.MonoidalCategory.leftUnitor_hom_apply,
      ModuleCat.MonoidalCategory.rightUnitor_hom_apply,
      moduleCup_sectionTensorMap, ModuleCat.hom_ofHom, tensorSectionsMap_tmul]
    exact (whiskerRight_app_tmulSection (X := X) (N := P) (U := ⊤) f x y).symm
  · intro M N P f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.MonoidalCategory.associator_hom_apply,
      ModuleCat.MonoidalCategory.leftUnitor_hom_apply,
      ModuleCat.MonoidalCategory.rightUnitor_hom_apply,
      moduleCup_sectionTensorMap, ModuleCat.hom_ofHom, tensorSectionsMap_tmul]
    exact (whiskerLeft_app_tmulSection (X := X) (M := P) (U := ⊤) f x y).symm
  · intro M N P
    apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intro x y z
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.MonoidalCategory.associator_hom_apply,
      ModuleCat.MonoidalCategory.leftUnitor_hom_apply,
      ModuleCat.MonoidalCategory.rightUnitor_hom_apply,
      moduleCup_sectionTensorMap, ModuleCat.hom_ofHom, tensorSectionsMap_tmul]
    exact associator_hom_app_tmulSection (X := X) (M := M) (N := N) (P := P)
      (U := ⊤) x y z
  · intro M
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro r s
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.MonoidalCategory.associator_hom_apply,
      ModuleCat.MonoidalCategory.leftUnitor_hom_apply,
      ModuleCat.MonoidalCategory.rightUnitor_hom_apply,
      moduleCup_sectionTensorMap, ModuleCat.hom_ofHom, tensorSectionsMap_tmul]
    exact (leftUnitor_hom_app_tmulSection (X := X) (M := M) (U := ⊤) r s).symm
  · intro M
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s r
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.MonoidalCategory.associator_hom_apply,
      ModuleCat.MonoidalCategory.leftUnitor_hom_apply,
      ModuleCat.MonoidalCategory.rightUnitor_hom_apply,
      moduleCup_sectionTensorMap, ModuleCat.hom_ofHom, tensorSectionsMap_tmul]
    exact (rightUnitor_hom_app_tmulSection (X := X) (M := M) (U := ⊤) r s).symm

end
end AlgebraicGeometry.Scheme.Modules
