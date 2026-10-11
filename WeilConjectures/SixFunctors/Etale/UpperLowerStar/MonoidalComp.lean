/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-!
# The composition isomorphism of étale pullbacks is monoidal

For sheaves on small étale sites with values in a symmetric monoidal closed Grothendieck abelian
category `A`, the composition isomorphism `(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` of pullbacks is
compatible with the comonoidal structures `δ` of the pullbacks
(`AlgebraicGeometry.Etale.upperStarComp_hom_app_tensor_comp_δ`): it is the conjugate of the
composition isomorphism of pushforwards, which is monoidal.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]
  {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` of pullbacks of étale sheaves is
compatible with the comonoidal structures:
```
(h₁ ≫ h₂)^*(X ⊗ Y) ───────────────▶ h₁^*h₂^*(X ⊗ Y) ──h₁^*δ──▶ h₁^*(h₂^*X ⊗ h₂^*Y)
        │ δ                                                            │ δ
        ▼                                                              ▼
(h₁ ≫ h₂)^*X ⊗ (h₁ ≫ h₂)^*Y ──────────────────────────────▶ h₁^*h₂^*X ⊗ h₁^*h₂^*Y
``` -/
@[reassoc]
lemma upperStarComp_hom_app_tensor_comp_δ (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂)
    (X Y : Sheaf R.smallEtaleTopology A) :
    (upperStarComp A h₁ h₂ h₁₂ hh).hom.app (X ⊗ Y) ≫
        (h₁)^*[A].map (δ (h₂)^*[A] X Y) ≫ δ (h₁)^*[A] _ _ =
      δ (h₁₂)^*[A] X Y ≫
        ((upperStarComp A h₁ h₂ h₁₂ hh).hom.app X ⊗ₘ (upperStarComp A h₁ h₂ h₁₂ hh).hom.app Y) := by
  have : NatTrans.IsMonoidal (lowerStarComp A h₁ h₂ h₁₂ hh).hom := by
    unfold lowerStarComp
    infer_instance
  have hconj : (upperStarComp A h₁ h₂ h₁₂ hh).hom =
      (conjugateEquiv ((upperStarLowerStarAdjunction _ h₂).comp
        (upperStarLowerStarAdjunction _ h₁)) (upperStarLowerStarAdjunction _ h₁₂)).symm
        (lowerStarComp A h₁ h₂ h₁₂ hh).hom := by
    rw [Equiv.eq_symm_apply, ← conjugateIsoEquiv_apply_hom,
      Etale.conjugateIsoEquiv_upperStarComp A h₁ h₂ h₁₂ hh]
  have := conjugateEquiv_symm_app_tensor_comp_δ ((upperStarLowerStarAdjunction _ h₂).comp
    (upperStarLowerStarAdjunction _ h₁)) (upperStarLowerStarAdjunction _ h₁₂)
    (lowerStarComp A h₁ h₂ h₁₂ hh).hom X Y
  rw [← hconj] at this
  simpa using this

end AlgebraicGeometry.Etale
