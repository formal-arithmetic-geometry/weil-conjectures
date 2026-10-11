/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd

/-!
# The composition isomorphism of étale pullbacks is monoidal

For sheaves of `Λ`-modules on small étale sites, the composition isomorphism
`(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` of pullbacks is compatible with the comonoidal structures `δ` of the
pullbacks: it is the conjugate of the monoidal composition isomorphism of pushforwards.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` of pullbacks of étale sheaves of
`Λ`-modules is compatible with the comonoidal structures:
```
(h₁ ≫ h₂)^*(X ⊗ Y) ───────────────▶ h₁^*h₂^*(X ⊗ Y) ──h₁^*δ──▶ h₁^*(h₂^*X ⊗ h₂^*Y)
        │ δ                                                            │ δ
        ▼                                                              ▼
(h₁ ≫ h₂)^*X ⊗ (h₁ ≫ h₂)^*Y ──────────────────────────────▶ h₁^*h₂^*X ⊗ h₁^*h₂^*Y
``` -/
@[reassoc]
lemma upperStarComp_hom_app_tensor_comp_δ (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂)
    (X Y : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom.app (X ⊗ Y) ≫
        (h₁)^*[ModuleCat.{u + 1} Λ].map (δ (h₂)^*[ModuleCat.{u + 1} Λ] X Y) ≫
          δ (h₁)^*[ModuleCat.{u + 1} Λ] _ _ =
      δ (h₁₂)^*[ModuleCat.{u + 1} Λ] X Y ≫
        ((upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom.app X ⊗ₘ
          (upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom.app Y) := by
  have hconj : (upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom =
      (conjugateEquiv ((upperStarLowerStarAdjunction _ h₂).comp
        (upperStarLowerStarAdjunction _ h₁)) (upperStarLowerStarAdjunction _ h₁₂)).symm
        (lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom := by
    rw [Equiv.eq_symm_apply, ← conjugateIsoEquiv_apply_hom,
      Etale.conjugateIsoEquiv_upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh]
  have := conjugateEquiv_symm_app_tensor_comp_δ ((upperStarLowerStarAdjunction _ h₂).comp
        (upperStarLowerStarAdjunction _ h₁)) (upperStarLowerStarAdjunction _ h₁₂)
        (lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom X Y
  rw [← hconj] at this
  simpa using this

end AlgebraicGeometry.Etale
