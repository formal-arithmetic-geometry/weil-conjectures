/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Gabber

/-!
# Forgetting the module structure commutes with the étale operations

For a commutative ring `Λ`, the forgetful functor from sheaves of `Λ`-modules to abelian sheaves
on the small étale site commutes with pullback, pushforward and constant sheaves. For pullback
this uses that `forget₂ : ModuleCat Λ ⥤ AddCommGrpCat` is a left adjoint (to coinduction), so
that it commutes with left Kan extensions and with sheafification.

## Main definitions

- `AlgebraicGeometry.Etale.upperStarSheafComposeForget₂Iso`
- `AlgebraicGeometry.Etale.lowerStarSheafComposeForget₂Iso`
- `AlgebraicGeometry.Etale.constantSheafSheafComposeForget₂Iso`
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale
open Scheme

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) (Λ : Type (u + 1)) [CommRing Λ]

/-- The forgetful functor from `Λ`-modules to abelian groups is left adjoint to coinduction. -/
instance isLeftAdjoint_forget₂_moduleCat :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
  (((ModuleCat.restrictCoextendScalarsAdj.{u + 1} (algebraMap ℤ Λ)).comp
    (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.toAdjunction).ofNatIsoLeft
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl))).isLeftAdjoint

/-- The étale pullback commutes with forgetting the module structure. -/
noncomputable def upperStarSheafComposeForget₂Iso :
    (g)^*[ModuleCat.{u + 1} Λ] ⋙
        sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
      sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
        (g)^*[AddCommGrpCat.{u + 1}] :=
  let F := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let L := (MorphismProperty.Over.pullback @Etale ⊤ g).op
  let e₁ := sheafComposeNatIso Z.smallEtaleTopology F
    (sheafificationAdjunction Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (sheafificationAdjunction Z.smallEtaleTopology AddCommGrpCat.{u + 1})
  have : ∀ F₁ : (MorphismProperty.Over @Etale ⊤ Y)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      F.PreservesLeftKanExtension F₁ L := fun F₁ ↦
    have : L.HasPointwiseLeftKanExtension F₁ := inferInstance
    have hF : PreservesColimitsOfSize.{u, u + 1} F :=
      (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits
    have : F.PreservesPointwiseLeftKanExtension F₁ L := fun c ↦
      have := (hF.preservesColimitsOfShape (J := CostructuredArrow L c)).preservesColimit
        (K := CostructuredArrow.proj L c ⋙ F₁)
      Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit _ _ _ c
    inferInstance
  let e₂ := Functor.lanCompIsoOfPreserves (L := L) (G := F)
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (sheafToPresheaf _ _)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L.lan e₁.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₂ _ ≪≫
      Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm

/-- The étale pushforward commutes with forgetting the module structure. -/
noncomputable def lowerStarSheafComposeForget₂Iso :
    (g)_*[ModuleCat.{u + 1} Λ] ⋙
        sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
      sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
        (g)_*[AddCommGrpCat.{u + 1}] :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- Constant sheaves commute with forgetting the module structure. -/
noncomputable def constantSheafSheafComposeForget₂Iso :
    constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
      forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ⋙
        constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    (sheafComposeNatIso Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
      (sheafificationAdjunction _ (ModuleCat.{u + 1} Λ))
      (sheafificationAdjunction _ AddCommGrpCat.{u + 1})).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)) _ ≪≫
    Functor.associator _ _ _
end AlgebraicGeometry.Etale
