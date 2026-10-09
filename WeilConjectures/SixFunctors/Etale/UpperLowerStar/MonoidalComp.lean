/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-!

# The composition isomorphisms of `g_*` and `g^*` are monoidal

For morphisms of schemes `h₁ : T ⟶ S` and `h₂ : S ⟶ R`, the composition isomorphism
`(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of pushforwards of étale sheaves
(`AlgebraicGeometry.Etale.lowerStarComp`) is a monoidal natural transformation, being the
composition isomorphism of pushforwards along continuous functors of sites. Its conjugate, the
composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of pullbacks
(`AlgebraicGeometry.Etale.upperStarComp`), is therefore compatible with the oplax monoidal
structures of the pullbacks.

## Main results

- `AlgebraicGeometry.Etale.isMonoidal_lowerStarComp_hom_of_isMonoidal_W`: `Etale.lowerStarComp`
  is monoidal, by `CategoryTheory.Functor.isMonoidal_sheafPushforwardContinuousComp'_hom`.
- `AlgebraicGeometry.Etale.upperStarComp_inv_app_tensor_comp_δ` and
  `AlgebraicGeometry.Etale.upperStarComp_hom_app_tensor_comp_δ`: `Etale.upperStarComp` is
  compatible with the comparison maps `δ : g^*(F ⊗ G) ⟶ g^*F ⊗ g^*G`.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h₁₂ : T ⟶ R) (hh₁₂ : h₁₂ = h₁ ≫ h₂)
  [(R.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(S.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(T.smallEtaleTopology.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of pushforwards of étale sheaves
is a monoidal natural transformation. -/
instance Etale.isMonoidal_lowerStarComp_hom_of_isMonoidal_W :
    NatTrans.IsMonoidal (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).hom :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ h₂).IsContinuous R.smallEtaleTopology
      S.smallEtaleTopology := Etale.isContinuous_overPullback h₂
  have : (MorphismProperty.Over.pullback @Etale ⊤ h₁).IsContinuous S.smallEtaleTopology
      T.smallEtaleTopology := Etale.isContinuous_overPullback h₁
  have : (MorphismProperty.Over.pullback @Etale ⊤ h₁₂).IsContinuous R.smallEtaleTopology
      T.smallEtaleTopology := Etale.isContinuous_overPullback h₁₂
  Functor.isMonoidal_sheafPushforwardContinuousComp'_hom (C := R.Etale) (D := S.Etale)
    (E := T.Etale) (A := A) (J := R.smallEtaleTopology) (K := S.smallEtaleTopology)
    (L := T.smallEtaleTopology) _

/-- The inverse of the composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of pullbacks of
étale sheaves is compatible with the comparison maps `δ` of the oplax monoidal pullbacks:
```
  h₁^*(h₂^*(X ⊗ Y)) ──h₁^*(δ)──▶ h₁^*(h₂^*X ⊗ h₂^*Y) ──δ──▶ h₁^*h₂^*X ⊗ h₁^*h₂^*Y
        │                                                          │
        │ inv                                                      │ inv ⊗ inv
        ▼                                                          ▼
  (h₁ ≫ h₂)^*(X ⊗ Y) ──────────────────δ───────────────▶ (h₁ ≫ h₂)^*X ⊗ (h₁ ≫ h₂)^*Y
```
It is the conjugate of the monoidal natural transformation `Etale.lowerStarComp`. -/
@[reassoc]
lemma Etale.upperStarComp_inv_app_tensor_comp_δ (X Y : Sheaf R.smallEtaleTopology A) :
    (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).inv.app (X ⊗ Y) ≫ δ (h₁₂)^*[A] X Y =
      (h₁)^*[A].map (δ (h₂)^*[A] X Y) ≫ δ (h₁)^*[A] _ _ ≫
        ((Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).inv.app X ⊗ₘ
          (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).inv.app Y) := by
  have := conjugateEquiv_symm_app_tensor_comp_δ (Etale.upperStarLowerStarAdjunction A h₁₂)
    ((Etale.upperStarLowerStarAdjunction A h₂).comp (Etale.upperStarLowerStarAdjunction A h₁))
    (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).inv X Y
  rw [comp_δ, Category.assoc] at this
  exact this

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of pullbacks of étale sheaves
is compatible with the comparison maps `δ` of the oplax monoidal pullbacks. -/
@[reassoc]
lemma Etale.upperStarComp_hom_app_tensor_comp_δ (X Y : Sheaf R.smallEtaleTopology A) :
    (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).hom.app (X ⊗ Y) ≫
        (h₁)^*[A].map (δ (h₂)^*[A] X Y) ≫ δ (h₁)^*[A] _ _ =
      δ (h₁₂)^*[A] X Y ≫ ((Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).hom.app X ⊗ₘ
        (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).hom.app Y) := by
  rw [← cancel_epi ((Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).inv.app (X ⊗ Y)),
    Iso.inv_hom_id_app_assoc, upperStarComp_inv_app_tensor_comp_δ_assoc,
    tensorHom_comp_tensorHom, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
  erw [id_tensorHom_id, Category.comp_id]

end AlgebraicGeometry
