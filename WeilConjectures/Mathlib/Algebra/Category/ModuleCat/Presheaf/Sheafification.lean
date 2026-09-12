/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The counit of the sheafification adjunction for presheaves of modules

Mathlib knows that the counit of the adjunction
`sheafification α ⊣ SheafOfModules.forget R ⋙ restrictScalars α` is an isomorphism; we package
it as a natural isomorphism.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

/-- Sheafifying the underlying presheaf of modules of a sheaf of modules gives the sheaf back:
the counit of the sheafification adjunction is a natural isomorphism. -/
noncomputable def sheafificationCounitIso :
    (SheafOfModules.forget.{v} R ⋙ restrictScalars α) ⋙ sheafification.{v} α ≅ 𝟭 _ :=
  asIso (sheafificationAdjunction.{v} α).counit

end PresheafOfModules
