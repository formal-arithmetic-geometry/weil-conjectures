/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Units of `g^* ⊣ g_*` along composites

The unit of the adjunction `(h₁ ≫ h₂)^* ⊣ (h₁ ≫ h₂)_*` on étale sheaves is the composite of the
units of `h₂` and `h₁`, up to the composition isomorphisms; consequently units which are
isomorphisms are stable under composition and cancellation, and the unit along an isomorphism
is an isomorphism.
-/

@[expose] public section

universe u u'

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The unit of `(h₁ ≫ h₂)^* ⊣ (h₁ ≫ h₂)_*` is the composite of the units of `h₂` and `h₁`, up to
the composition isomorphisms. -/
theorem Etale.unit_app_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (F : Sheaf R.smallEtaleTopology A) :
    (upperStarLowerStarAdjunction A (h₁ ≫ h₂)).unit.app F ≫ (lowerStarComp A h₁ h₂).inv.app _ =
      ((upperStarLowerStarAdjunction A h₂).unit.app F ≫
        (h₂)_*[A].map ((upperStarLowerStarAdjunction A h₁).unit.app ((h₂)^*[A].obj F))) ≫
        (h₂)_*[A].map ((h₁)_*[A].map
          (((conjugateEquiv (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
            ((upperStarLowerStarAdjunction A h₂).comp (upperStarLowerStarAdjunction A h₁))).symm
              (lowerStarComp A h₁ h₂).inv).app F)) := by
  rw [unit_conjugateEquiv_symm, Adjunction.comp_unit_app]
  rfl

/-- If the units of `h₁ ≫ h₂` at `F` and of `h₁` at `h₂^* F` are isomorphisms, so is the unit of
`h₂` at `F`. -/
theorem Etale.isIso_unit_app_of_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (F : Sheaf R.smallEtaleTopology A)
    [IsIso ((upperStarLowerStarAdjunction A (h₁ ≫ h₂)).unit.app F)]
    [IsIso ((upperStarLowerStarAdjunction A h₁).unit.app ((h₂)^*[A].obj F))] :
    IsIso ((upperStarLowerStarAdjunction A h₂).unit.app F) := by
  have h := Etale.unit_app_comp A h₁ h₂ F
  have : IsIso ((upperStarLowerStarAdjunction A (h₁ ≫ h₂)).unit.app F ≫
      (lowerStarComp A h₁ h₂).inv.app _) := inferInstance
  rw [h] at this
  simpa only [isIso_comp_right_iff] using this

/-- If the units of `h₂` at `F` and of `h₁` at `h₂^* F` are isomorphisms, so is the unit of
`h₁ ≫ h₂` at `F`. -/
theorem Etale.isIso_unit_app_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (F : Sheaf R.smallEtaleTopology A)
    [IsIso ((upperStarLowerStarAdjunction A h₂).unit.app F)]
    [IsIso ((upperStarLowerStarAdjunction A h₁).unit.app ((h₂)^*[A].obj F))] :
    IsIso ((upperStarLowerStarAdjunction A (h₁ ≫ h₂)).unit.app F) := by
  have h := Etale.unit_app_comp A h₁ h₂ F
  have : IsIso ((upperStarLowerStarAdjunction A (h₁ ≫ h₂)).unit.app F ≫
      (lowerStarComp A h₁ h₂ (h₁ ≫ h₂) rfl).inv.app _) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _ ((lowerStarComp A h₁ h₂ (h₁ ≫ h₂) rfl).inv.app _)

/-- The unit of `g^* ⊣ g_*` along an isomorphism `g` is an isomorphism. -/
instance Etale.isIso_unit_app_of_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (F : Sheaf Y.smallEtaleTopology A) :
    IsIso ((upperStarLowerStarAdjunction A g).unit.app F) := by
  have := (upperStarLowerStarAdjunction A g).isEquivalence_left_of_isEquivalence_right
  infer_instance

end AlgebraicGeometry
