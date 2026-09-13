/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Sheafification of presheaves of modules that are already sheaves

Let `α : R₀ ⟶ R.val` be a locally bijective morphism from a presheaf of rings to (the underlying
presheaf of) a sheaf of rings on a site `(C, J)`. The sheafification of presheaves of modules
`PresheafOfModules R₀ ⥤ SheafOfModules R` is left adjoint to the forgetful functor, and its
counit is always an isomorphism. We record that the unit is an isomorphism at a presheaf of
modules whose underlying presheaf is a sheaf, so that if *every* presheaf of `R₀`-modules is a
sheaf — as happens over a topological space with at most one point — the sheafification is an
equivalence of categories.

## Main declarations

- `PresheafOfModules.isIso_sheafificationAdjunction_unit_app`: the unit of the sheafification
  adjunction is an isomorphism at a presheaf of modules which is a sheaf.
- `PresheafOfModules.sheafificationEquivalenceOfIsSheaf`: if every presheaf of `R₀`-modules is a
  sheaf, the sheafification is an equivalence of categories.

-/

@[expose] public section

universe v v' u u'

open CategoryTheory

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

namespace PresheafOfModules

/-- The unit of the sheafification adjunction for presheaves of modules is an isomorphism at a
presheaf of modules whose underlying presheaf is already a sheaf. -/
theorem isIso_sheafificationAdjunction_unit_app (M₀ : PresheafOfModules.{v} R₀)
    (h : Presheaf.IsSheaf J M₀.presheaf) :
    IsIso ((sheafificationAdjunction α).unit.app M₀) := by
  have : IsIso ((toPresheaf _).map ((sheafificationAdjunction α).unit.app M₀)) := by
    rw [toPresheaf_map_sheafificationAdjunction_unit_app]
    exact isIso_toSheafify _ h
  exact isIso_of_reflects_iso _ (toPresheaf _)

/-- **If every presheaf of `R₀`-modules is a sheaf, the sheafification of presheaves of modules
is an equivalence of categories**, quasi-inverse to the forgetful functor. -/
noncomputable def sheafificationEquivalenceOfIsSheaf
    (h : ∀ M₀ : PresheafOfModules.{v} R₀, Presheaf.IsSheaf J M₀.presheaf) :
    PresheafOfModules.{v} R₀ ≌ SheafOfModules.{v} R :=
  have := fun M₀ ↦ isIso_sheafificationAdjunction_unit_app α M₀ (h M₀)
  (sheafificationAdjunction α).toEquivalence

end PresheafOfModules
