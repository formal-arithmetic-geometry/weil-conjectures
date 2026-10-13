/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Paper.SiteSheafificationSectionsLocal

/-! # A locally injective map into a sheaf induces an injective map on sheafification

Source: literature/stacks-project/sites.tex, Theorem 00WB and Lemma 00WK,
with sites-modules.tex Lemma 03CY
(blueprint: lem-weil-pbc-site-module-sheafification-lift-injective).
-/

@[expose] public section

universe v u₁ v₁ u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A locally injective morphism from a presheaf of modules to a sheaf of modules
induces an injective morphism after sheafification.
Source: literature/stacks-project/sites.tex, Theorem 00WB and Lemma 00WK,
with sites-modules.tex Lemma 03CY
(blueprint: lem-weil-pbc-site-module-sheafification-lift-injective).
The proof uses the local-sections description of sheafification, refinement and
composition of coverings, compatibility of module sheafification with underlying
sheaves of sets, and separatedness of sheaves.
-/
lemma site_module_sheafification_lift_injective
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasWeakSheafify J AddCommGrpCat.{v}]
    {P : PresheafOfModules.{v} R.obj}
    {F : SheafOfModules.{v} R}
    (f : P ⟶ (SheafOfModules.forget R).obj F)
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R.obj).map f)] :
    (∀ (X : Cᵒᵖ), Function.Injective (((SheafOfModules.toSheaf R).map
      ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm f)).hom.app X)) ∧
      Mono ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm f) := by
  have fac : CategoryTheory.toSheafify J P.presheaf ≫
      ((SheafOfModules.toSheaf R).map
        ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm f)).hom =
      (PresheafOfModules.toPresheaf R.obj).map f :=
    (PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def (𝟙 R.obj)
      ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm f)).symm.trans
      (congrArg (PresheafOfModules.toPresheaf R.obj).map
        ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).apply_symm_apply f))
  have : Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P.presheaf ≫
      ((SheafOfModules.toSheaf R).map
        ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm f)).hom) := by
    rw [fac]; assumption
  have := Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J
    (CategoryTheory.toSheafify J P.presheaf)
    ((SheafOfModules.toSheaf R).map
        ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm f)).hom
  have hinj := (Sheaf.isLocallyInjective_iff_injective _).1 this
  refine ⟨hinj, ?_⟩
  have := Sheaf.mono_of_injective _ hinj
  exact (SheafOfModules.toSheaf R).mono_of_mono_map this

end CategoryTheory
