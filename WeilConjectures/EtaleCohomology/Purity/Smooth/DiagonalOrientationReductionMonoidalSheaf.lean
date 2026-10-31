/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-!
# Extension of scalars of étale sheaves commutes monoidally with pullback

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings and `e : U ⟶ X` a morphism of schemes.
The extension of scalars `F = Λ' ⊗_Λ -` of étale sheaves commutes with the pullback:
`F_X ⋙ e^* ≅ e^* ⋙ F_U` (`AlgebraicGeometry.Etale.extendScalarsUpperStarIso`), the conjugate of
the identification `e_* ⋙ Res ≅ Res ⋙ e_*` of the right adjoints. This isomorphism is monoidal
(`AlgebraicGeometry.Etale.isMonoidal_extendScalarsUpperStarIso_hom`), since the identification of
the right adjoints is monoidal for their lax structures.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal

section SheafCompose

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
  {A : Type*} [Category A] [MonoidalCategory A]
  {B : Type*} [Category B] [MonoidalCategory B]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B]
  (G : A ⥤ B) [J.HasSheafCompose G] [G.LaxMonoidal]

attribute [local instance] Sheaf.monoidalCategory

/-- The componentwise form of `CategoryTheory.ε_sheafToPresheaf_comp_map_ε_sheafCompose`. -/
@[reassoc]
lemma ε_sheafToPresheaf_app_comp_ε_sheafCompose_app (U : Cᵒᵖ) :
    (ε (sheafToPresheaf J B)).app U ≫ (ε (sheafCompose J G)).hom.app U =
      ε G ≫ G.map ((ε (sheafToPresheaf J A)).app U) := by
  simpa using congr_app (ε_sheafToPresheaf_comp_map_ε_sheafCompose J G) U

/-- The componentwise form of `CategoryTheory.μ_sheafToPresheaf_comp_map_μ_sheafCompose`. -/
@[reassoc]
lemma μ_sheafToPresheaf_app_comp_μ_sheafCompose_app (P Q : Sheaf J A) (U : Cᵒᵖ) :
    (μ (sheafToPresheaf J B) ((sheafCompose J G).obj P) ((sheafCompose J G).obj Q)).app U ≫
        (μ (sheafCompose J G) P Q).hom.app U =
      μ G (P.obj.obj U) (Q.obj.obj U) ≫ G.map ((μ (sheafToPresheaf J A) P Q).app U) := by
  simpa using congr_app (μ_sheafToPresheaf_comp_map_μ_sheafCompose J G P Q) U

end SheafCompose

end CategoryTheory

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {U X : Scheme.{u}}
  (e : U ⟶ X)

/-- The adjunction `F_X ⋙ e^* ⊣ e_* ⋙ Res_X`. -/
noncomputable abbrev extendScalarsUpperStarAdjunction :
    Sheaf.extendScalars X.smallEtaleTopology ρ ⋙ (e)^*[ModuleCat.{u + 1} Λ'] ⊣
      (e)_*[ModuleCat.{u + 1} Λ'] ⋙ Sheaf.restrictScalars X.smallEtaleTopology ρ :=
  (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') e)

/-- The adjunction `e^* ⋙ F_U ⊣ Res_U ⋙ e_*`. -/
noncomputable abbrev upperStarExtendScalarsAdjunction :
    (e)^*[ModuleCat.{u + 1} Λ] ⋙ Sheaf.extendScalars U.smallEtaleTopology ρ ⊣
      Sheaf.restrictScalars U.smallEtaleTopology ρ ⋙ (e)_*[ModuleCat.{u + 1} Λ] :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e).comp
    (Sheaf.extendScalarsAdjunction U.smallEtaleTopology ρ)

/-- **Extension of scalars commutes with pullback**: `F_X ⋙ e^* ≅ e^* ⋙ F_U`, the conjugate of
the identification `e_* ⋙ Res ≅ Res ⋙ e_*`. -/
noncomputable def extendScalarsUpperStarIso :
    Sheaf.extendScalars X.smallEtaleTopology ρ ⋙ (e)^*[ModuleCat.{u + 1} Λ'] ≅
      (e)^*[ModuleCat.{u + 1} Λ] ⋙ Sheaf.extendScalars U.smallEtaleTopology ρ where
  hom := (conjugateEquiv (upperStarExtendScalarsAdjunction ρ e)
    (extendScalarsUpperStarAdjunction ρ e)).symm (lowerStarCompRestrictScalarsIso ρ e).inv
  inv := (conjugateEquiv (extendScalarsUpperStarAdjunction ρ e)
    (upperStarExtendScalarsAdjunction ρ e)).symm (lowerStarCompRestrictScalarsIso ρ e).hom
  hom_inv_id := by
    rw [conjugateEquiv_symm_comp, Iso.hom_inv_id, conjugateEquiv_symm_id]
  inv_hom_id := by
    rw [conjugateEquiv_symm_comp, Iso.inv_hom_id, conjugateEquiv_symm_id]

lemma extendScalarsUpperStarIso_inv :
    (extendScalarsUpperStarIso ρ e).inv = (conjugateEquiv (extendScalarsUpperStarAdjunction ρ e)
      (upperStarExtendScalarsAdjunction ρ e)).symm (lowerStarCompRestrictScalarsIso ρ e).hom :=
  rfl

/-- The commutation `F_X ⋙ e^* ≅ e^* ⋙ F_U` is the mate, along the adjunctions `F ⊣ Res`, of the
commutation `Res ⋙ e^* ≅ e^* ⋙ Res` (`AlgebraicGeometry.Etale.upperStarRestrictScalarsIso`):
both come from the identification `e_* ⋙ Res ≅ Res ⋙ e_*`. -/
lemma mateEquiv_extendScalarsUpperStarIso_inv :
    mateEquiv (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ)
        (Sheaf.extendScalarsAdjunction U.smallEtaleTopology ρ) (extendScalarsUpperStarIso ρ e).inv =
      (upperStarRestrictScalarsIso ρ e).hom := by
  have h := iterated_mateEquiv_conjugateEquiv
    (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ)
    (Sheaf.extendScalarsAdjunction U.smallEtaleTopology ρ)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') e) (extendScalarsUpperStarIso ρ e).inv
  rw [extendScalarsUpperStarIso_inv, Equiv.apply_symm_apply] at h
  rw [upperStarRestrictScalarsIso, asIso_hom, upperStarRestrictScalars, ← h]
  exact ((mateEquiv _ _).symm_apply_apply _).symm

section Monoidal

open Functor.LaxMonoidal Functor.OplaxMonoidal

attribute [local instance] Sheaf.monoidalCategory

/-- The identification `e_* ⋙ Res ≅ Res ⋙ e_*` is monoidal for the composite lax structures:
on underlying presheaves both tensor maps are the tensor map of restriction of scalars of
modules, evaluated on the sections over the base change. -/
instance isMonoidal_lowerStarCompRestrictScalarsIso_hom :
    NatTrans.IsMonoidal (lowerStarCompRestrictScalarsIso ρ e).hom where
  unit := by
    simp only [lowerStarCompRestrictScalarsIso, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
      Functor.LaxMonoidal.comp_ε]
    apply Sheaf.hom_ext_of_ε_comp
    ext V : 2
    simp only [NatTrans.comp_app, ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
      sheafCompose_map_hom, Functor.whiskerRight_app]
    rw [ε_sheafToPresheaf_app_comp_ε_sheafCompose_app_assoc, ← Functor.map_comp, ← Category.assoc]
    erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app,
      Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app,
      Etale.lowerStar_map_hom_app,
      ε_sheafToPresheaf_app_comp_ε_sheafCompose_app]
  tensor A B := by
    simp only [lowerStarCompRestrictScalarsIso, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
      Functor.LaxMonoidal.comp_μ, MonoidalCategory.id_tensorHom_id, Category.id_comp]
    apply Sheaf.hom_ext_of_μ_comp
    ext V : 2
    simp only [NatTrans.comp_app, ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
      sheafCompose_map_hom, Functor.whiskerRight_app, Functor.comp_obj]
    rw [μ_sheafToPresheaf_app_comp_μ_sheafCompose_app_assoc, ← Functor.map_comp]
    have h₁ : (μ (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
        ((e)_*[ModuleCat.{u + 1} Λ'].obj A) ((e)_*[ModuleCat.{u + 1} Λ'].obj B)).app V ≫
          (μ (e)_*[ModuleCat.{u + 1} Λ'] A B).hom.app V =
        (μ (sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ')) A B).app
          ((MorphismProperty.Over.pullback @Etale ⊤ e).op.obj V) :=
      Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
        (MorphismProperty.Over.pullback @Etale ⊤ e) (ModuleCat.{u + 1} Λ')
        (X.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale) A B V
    have h₂ : (μ (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj ((e)_*[ModuleCat.{u + 1} Λ'].obj A))
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj
          ((e)_*[ModuleCat.{u + 1} Λ'].obj B))).app V ≫
          (μ (e)_*[ModuleCat.{u + 1} Λ] ((Sheaf.restrictScalars U.smallEtaleTopology ρ).obj A)
            ((Sheaf.restrictScalars U.smallEtaleTopology ρ).obj B)).hom.app V =
        (μ (sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
          ((Sheaf.restrictScalars U.smallEtaleTopology ρ).obj A)
          ((Sheaf.restrictScalars U.smallEtaleTopology ρ).obj B)).app
          ((MorphismProperty.Over.pullback @Etale ⊤ e).op.obj V) :=
      Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
        (MorphismProperty.Over.pullback @Etale ⊤ e) (ModuleCat.{u + 1} Λ)
        (X.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
        ((Sheaf.restrictScalars U.smallEtaleTopology ρ).obj A)
        ((Sheaf.restrictScalars U.smallEtaleTopology ρ).obj B) V
    rw [h₁, reassoc_of% h₂, Etale.lowerStar_map_hom_app]
    exact (μ_sheafToPresheaf_app_comp_μ_sheafCompose_app U.smallEtaleTopology
      (ModuleCat.restrictScalars ρ) A B _).symm

/-- The commutation `F_X ⋙ e^* ≅ e^* ⋙ F_U` of extension of scalars with pullback is monoidal
(inverse direction): it is the conjugate of the monoidal identification `e_* ⋙ Res ≅ Res ⋙ e_*`
of the right adjoints. -/
theorem isMonoidal_extendScalarsUpperStarIso_inv :
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ (extendScalarsUpperStarIso ρ e).inv
      (Functor.Monoidal.instComp _ _).toLaxMonoidal (Functor.Monoidal.instComp _ _).toLaxMonoidal :=
  isMonoidal_conjugateEquiv_symm (extendScalarsUpperStarAdjunction ρ e)
    (upperStarExtendScalarsAdjunction ρ e) (lowerStarCompRestrictScalarsIso ρ e).hom

/-- **Extension of scalars commutes monoidally with pullback**: the commutation
`F_X ⋙ e^* ≅ e^* ⋙ F_U` is a monoidal natural isomorphism. -/
theorem isMonoidal_extendScalarsUpperStarIso_hom :
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ (extendScalarsUpperStarIso ρ e).hom
      (Functor.Monoidal.instComp _ _).toLaxMonoidal (Functor.Monoidal.instComp _ _).toLaxMonoidal :=
  isMonoidal_conjugateEquiv_symm (upperStarExtendScalarsAdjunction ρ e)
    (extendScalarsUpperStarAdjunction ρ e) (lowerStarCompRestrictScalarsIso ρ e).inv

end Monoidal

end AlgebraicGeometry.Etale
