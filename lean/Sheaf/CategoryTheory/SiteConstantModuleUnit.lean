/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.CategoryTheory.SiteConstantModuleFunctor

/-! # The constant-module sheafification unit

Source: Stacks Project, Modules on Sites, Tags 03CY and 093T.
(blueprint: lem-sf-constant-module-unit-locally-bijective).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ]

/-- The underlying additive sheafification unit of a constant module. -/
def siteConstantModuleUnit (M : ModuleCat.{u} Λ) :
    (Functor.const Cᵒᵖ).obj ((forget₂ (ModuleCat Λ) AddCommGrpCat).obj M) ⟶
      ((siteConstantModuleFunctor J Λ).obj M).val.presheaf :=
  toSheafify J ((siteConstantModulePresheaf (C := C) Λ).obj M).presheaf

instance (M : ModuleCat.{u} Λ) :
    Presheaf.IsLocallyInjective J (siteConstantModuleUnit J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J
    (toSheafify J ((siteConstantModulePresheaf (C := C) Λ).obj M).presheaf))

instance (M : ModuleCat.{u} Λ) :
    Presheaf.IsLocallySurjective J (siteConstantModuleUnit J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    (toSheafify J ((siteConstantModulePresheaf (C := C) Λ).obj M).presheaf))

lemma siteConstantModuleUnit_naturality {M N : ModuleCat.{u} Λ} (f : M ⟶ N)
    (U : Cᵒᵖ) (x : M) :
    ((siteConstantModuleFunctor J Λ).map f).val.app U
      ((siteConstantModuleUnit J Λ M).app U x) =
        (siteConstantModuleUnit J Λ N).app U (f x) := by
  have h := toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map
    ((siteConstantModulePresheaf (C := C) Λ).map f))
  exact (ConcreteCategory.congr_hom (congr_app h U) x).symm

/-- The constant-module sheaf, viewed as a presheaf of modules over the original ring. -/
def siteConstantModuleSections (M : ModuleCat.{u} Λ) : Cᵒᵖ ⥤ ModuleCat.{u} Λ where
  obj U := ((PresheafOfModules.restrictScalars
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).obj
      ((siteConstantModuleFunctor J Λ).obj M).val).obj U
  map f := ((PresheafOfModules.restrictScalars
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).obj
      ((siteConstantModuleFunctor J Λ).obj M).val).map f
  map_id U := by ext x; simp; rfl
  map_comp f g := by ext x; simp; rfl

/-- The linear form of the constant-module sheafification unit. -/
def siteConstantModuleUnitSections (M : ModuleCat.{u} Λ) :
    (Functor.const Cᵒᵖ).obj M ⟶ siteConstantModuleSections J Λ M where
  app U := ((PresheafOfModules.sheafificationAdjunction
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).unit.app
      ((siteConstantModulePresheaf (C := C) Λ).obj M)).app U
  naturality {U V} f := by
    ext x
    exact NatTrans.naturality_apply (siteConstantModuleUnit J Λ M) f x

instance (M : ModuleCat.{u} Λ) :
    Presheaf.IsLocallyInjective J (siteConstantModuleUnitSections J Λ M) where
  equalizerSieve_mem {U} x y h := by
    exact Presheaf.equalizerSieve_mem J (siteConstantModuleUnit J Λ M) x y h

instance (M : ModuleCat.{u} Λ) :
    Presheaf.IsLocallySurjective J (siteConstantModuleUnitSections J Λ M) where
  imageSieve_mem {U} x := by
    exact Presheaf.imageSieve_mem J (siteConstantModuleUnit J Λ M) x

/-- The linear unit is locally bijective on underlying sections.
Source: Stacks Project, Modules on Sites, Tag 03CY.
(blueprint: lem-sf-constant-module-unit-locally-bijective). -/
theorem siteConstantModuleUnitSections_locallyBijective (M : ModuleCat.{u} Λ) :
    Presheaf.IsLocallyInjective J (siteConstantModuleUnitSections J Λ M) ∧
      Presheaf.IsLocallySurjective J (siteConstantModuleUnitSections J Λ M) :=
  ⟨inferInstance, inferInstance⟩

end CategoryTheory
