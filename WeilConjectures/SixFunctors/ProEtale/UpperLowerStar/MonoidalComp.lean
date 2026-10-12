/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Monoidal

/-!
# The composition isomorphism of pro-étale pullbacks is oplax monoidal

For `h₁ : T ⟶ S` and `h₂ : S ⟶ R`, the composition isomorphism
`(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` of pullbacks of pro-étale sheaves
(`AlgebraicGeometry.ProEtale.upperStarComp`) is compatible with the oplax monoidal structures of
the pullbacks: it is the conjugate of the composition isomorphism of the pushforwards, which is
monoidal for their lax monoidal structures. This holds for an arbitrary coefficient category
`A`; `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.MonoidalIso` treats the strong monoidal
case of Weil coefficients.

## Main results

- `AlgebraicGeometry.ProEtale.upperStarComp_hom_app_tensor_comp_δ`: the composition isomorphism
  of pullbacks commutes with the comparison maps `δ`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
  [((Scheme.ProEt.topology R).W (A := A)).IsMonoidal]
  [((Scheme.ProEt.topology S).W (A := A)).IsMonoidal]
  [((Scheme.ProEt.topology T).W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The composition isomorphism `h₁_* ⋙ h₂_* ≅ (h₁ ≫ h₂)_*` of pushforwards of pro-étale sheaves
is monoidal. -/
instance ProEtale.isMonoidal_lowerStarComp_hom' :
    NatTrans.IsMonoidal (ProEtale.lowerStarComp A h₁ h₂).hom := by
  unfold ProEtale.lowerStarComp
  infer_instance

/-- The inverse of the composition isomorphism of pushforwards of pro-étale sheaves is
monoidal. -/
instance ProEtale.isMonoidal_lowerStarComp_inv' :
    NatTrans.IsMonoidal (ProEtale.lowerStarComp A h₁ h₂).inv :=
  inferInstance

/-- The composition isomorphism `h₂^* ⋙ h₁^* ≅ (h₁ ≫ h₂)^*` of pullbacks commutes with the
comparison maps `δ` of the oplax monoidal pullbacks:
```
  h₁^* h₂^* (X ⊗ Y) ──────────────────▶ (h₁ ≫ h₂)^* (X ⊗ Y)
        │ h₁^* δ ≫ δ                         │ δ
        ▼                                    ▼
  h₁^* h₂^* X ⊗ h₁^* h₂^* Y ─────▶ (h₁ ≫ h₂)^* X ⊗ (h₁ ≫ h₂)^* Y
```
-/
@[reassoc]
lemma ProEtale.upperStarComp_inv_app_tensor_comp_δ
    (X Y : Sheaf (Scheme.ProEt.topology R) A) :
    (ProEtale.upperStarComp A h₁ h₂).inv.app (X ⊗ Y) ≫ δ (h₁ ≫ h₂)^*[A] X Y =
      (h₁)^*[A].map (δ (h₂)^*[A] X Y) ≫ δ (h₁)^*[A] _ _ ≫
        ((ProEtale.upperStarComp A h₁ h₂).inv.app X ⊗ₘ
          (ProEtale.upperStarComp A h₁ h₂).inv.app Y) := by
  have := conjugateEquiv_symm_app_tensor_comp_δ (ProEtale.upperStarLowerStarAdjunction A (h₁ ≫ h₂))
    ((ProEtale.upperStarLowerStarAdjunction A h₂).comp
      (ProEtale.upperStarLowerStarAdjunction A h₁))
    (ProEtale.lowerStarComp A h₁ h₂).inv X Y
  rw [comp_δ] at this
  simp only [Category.assoc] at this
  exact this

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` of pullbacks commutes with the
comparison maps `δ` of the oplax monoidal pullbacks. -/
@[reassoc]
lemma ProEtale.upperStarComp_hom_app_tensor_comp_δ
    (X Y : Sheaf (Scheme.ProEt.topology R) A) :
    δ (h₁ ≫ h₂)^*[A] X Y ≫ ((ProEtale.upperStarComp A h₁ h₂).hom.app X ⊗ₘ
        (ProEtale.upperStarComp A h₁ h₂).hom.app Y) =
      (ProEtale.upperStarComp A h₁ h₂).hom.app (X ⊗ Y) ≫
        (h₁)^*[A].map (δ (h₂)^*[A] X Y) ≫ δ (h₁)^*[A] _ _ := by
  rw [← cancel_epi ((ProEtale.upperStarComp A h₁ h₂).inv.app (X ⊗ Y)),
    upperStarComp_inv_app_tensor_comp_δ_assoc, Iso.inv_hom_id_app_assoc,
    tensorHom_comp_tensorHom, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
  erw [id_tensorHom_id, Category.comp_id]

end AlgebraicGeometry
