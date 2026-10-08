/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Sheaves of modules form a Grothendieck abelian category

Let `R` be a sheaf of rings on a small site `(C, J)`. The category of sheaves of `R`-modules is
a Grothendieck abelian category:

* filtered colimits are exact, because the functor `SheafOfModules.toSheaf R` to sheaves of
  abelian groups preserves colimits and finite limits, reflects isomorphisms, and filtered
  colimits are exact in sheaves of abelian groups;
* the sheafifications of the free presheaves of modules on the representable presheaves form a
  small separating family, since the right adjoint of the sheafification is faithful.

## Main results

- `SheafOfModules.isSeparating_sheafification_freeYoneda`: the sheafified free modules on the
  representable presheaves form a separating family.
- `SheafOfModules.isGrothendieckAbelian`: `SheafOfModules.{u} R` is Grothendieck abelian.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The sheafifications of the free presheaves of modules `R[yoneda X]` on the representable
presheaves form a separating family of sheaves of `R`-modules. -/
lemma isSeparating_sheafification_freeYoneda :
    ObjectProperty.IsSeparating (.ofObj fun X : C ↦ (PresheafOfModules.sheafification
      (𝟙 R.obj)).obj ((PresheafOfModules.free R.obj).obj (yoneda.obj X))) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
  intro M N f g hfg
  refine (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map_injective
    (PresheafOfModules.freeYoneda.isSeparating R.obj _ _ ?_)
  rintro _ ⟨X⟩ a
  apply (adj.homEquiv _ _).symm.injective
  have h := hfg _ (ObjectProperty.ofObj_apply _ X) ((adj.homEquiv _ _).symm a)
  rw [← Adjunction.homEquiv_naturality_right_symm,
    ← Adjunction.homEquiv_naturality_right_symm] at h
  exact h

/-- **Sheaves of modules form a Grothendieck abelian category.** -/
theorem isGrothendieckAbelian : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) := by
  have : HasFilteredColimitsOfSize.{u, u} (SheafOfModules.{u} R) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{u, u} (SheafOfModules.{u} R) :=
    ⟨fun K _ _ ↦ HasExactColimitsOfShape.domain_of_functor K (toSheaf.{u} R)⟩
  have : HasSeparator (SheafOfModules.{u} R) :=
    ⟨_, (isSeparating_sheafification_freeYoneda R).isSeparator_coproduct⟩
  exact {}

end SheafOfModules
