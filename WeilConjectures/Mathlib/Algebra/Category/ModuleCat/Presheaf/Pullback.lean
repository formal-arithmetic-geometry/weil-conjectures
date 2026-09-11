/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal

/-!
# The pullback of presheaves of modules is oplax monoidal

Let `F : C ⥤ D` be a functor, `R : Dᵒᵖ ⥤ CommRingCat` and `S : Cᵒᵖ ⥤ CommRingCat` presheaves
of commutative rings, and `φ : S ⋙ forget₂ _ _ ⟶ (F.op ⋙ R) ⋙ forget₂ _ _` a morphism of the
underlying presheaves of rings. When `PresheafOfModules.pushforward φ` has a left adjoint,
we show that `PresheafOfModules.pullback φ` is oplax monoidal, as the left adjoint of a lax
monoidal functor. Note that at the level of presheaves this functor is a left Kan extension,
which does not preserve the objectwise tensor product, so oplax is the correct statement here.

## Main declarations

* `PresheafOfModules.pullbackOplaxMonoidal`: `pullback φ` is oplax monoidal.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⋙ forget₂ CommRingCat RingCat ⟶ (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)

/-- When it exists, the pullback of presheaves of modules along `φ` is oplax monoidal, being
the left adjoint of the lax monoidal functor `pushforward φ`. Using this entry point makes
`pullbackPushforwardAdjunction φ` a monoidal adjunction. -/
noncomputable instance pullbackOplaxMonoidal
    [(pushforward.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
      (S := S ⋙ forget₂ CommRingCat RingCat) φ).IsRightAdjoint] :
    (pullback.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
      (S := S ⋙ forget₂ CommRingCat RingCat) φ).OplaxMonoidal :=
  (pullbackPushforwardAdjunction.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat) φ).leftAdjointOplaxMonoidal

end PresheafOfModules
