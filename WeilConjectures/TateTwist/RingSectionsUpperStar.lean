/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TateTwist.RootsOfUnityPullback

/-!
# Pullback of sheaves of the form `U ↦ F(Γ(U, 𝒪_U))`

Let `F : CommRingCat ⥤ Ab` be a functor such that, for every scheme `X`, the presheaf
`F_X : U ↦ F(Γ(U, 𝒪_U))` on the small pro-étale site `X_proét` is a sheaf (for instance
`F = μ_N`, see `WeilConjectures.TateTwist.RootsOfUnityUpperStar`). For an arbitrary morphism of
schemes `f : X ⟶ Y`, pulling back functions along the projections `V ×_Y X ⟶ V` defines a map
`F_Y ⟶ f_* F_X`, whose adjoint is a comparison map
```
φ_f : f^* F_Y ⟶ F_X
```
(`AlgebraicGeometry.ProEtale.upperStarRingSectionsSheafHom`). This file proves the formal
properties of `φ`:

* it is compatible with composition: `φ_{h₁ ≫ h₂} = φ_{h₁} ∘ h₁^* φ_{h₂}` up to the composition
  isomorphism `(h₁ ≫ h₂)^* ≅ h₁^* h₂^*`
  (`AlgebraicGeometry.ProEtale.upperStarRingSectionsSheafHom_comp`). Both sides are adjoint to
  maps `F_R ⟶ (h₁ ≫ h₂)_* F_T` given by pulling back functions, which agree since the projections
  `V ×_R T ⟶ V` factor through `V ×_R S`;
* it is natural in `F` (`AlgebraicGeometry.ProEtale.upperStar_map_ringSectionsSheafMap_comp`);
* it is an isomorphism for `f` weakly étale
  (`AlgebraicGeometry.ProEtale.isIso_upperStarRingSectionsSheafHom_of_weaklyEtale`): then `f^*` is
  restriction along the localization functor `X_proét ⥤ Y_proét`, which sends `F_Y` to `F_X`,
  and `φ_f` becomes the identity, the unit `V ⟶ V ×_Y X` of the localization being a section of
  the projection.

## Main definitions

- `AlgebraicGeometry.ProEtale.ringSectionsPresheaf F X`: the presheaf `U ↦ F(Γ(U, 𝒪_U))`.
- `AlgebraicGeometry.ProEtale.upperStarRingSectionsSheafHom`: the comparison `f^* F_Y ⟶ F_X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory

/-- For conjugate natural transformations `α : L₂ ⟶ L₁` and `β : R₁ ⟶ R₂` with respect to
adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂`, the adjoint of `z ≫ β` is `α` followed by the adjoint of
`z`. -/
lemma homEquiv_symm_comp_conjugateEquiv_app {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) {c : C}
    {d : D} (z : c ⟶ R₁.obj d) :
    (adj₂.homEquiv _ _).symm (z ≫ (conjugateEquiv adj₁ adj₂ α).app d) =
      α.app c ≫ (adj₁.homEquiv _ _).symm z := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    conjugateEquiv_counit, α.naturality_assoc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The adjunction `g^* ⊣ g_*` is compatible with composition: for `h₁ : T ⟶ S` and
`h₂ : S ⟶ R`, the adjoint of `x ≫ h₂_* y` (followed by `h₂_* h₁_* ≅ (h₁ ≫ h₂)_*`) is the
composition isomorphism `(h₁ ≫ h₂)^* ≅ h₁^* h₂^*` followed by `h₁^*` of the adjoint of `x` and
the adjoint of `y`. -/
lemma upperStarLowerStarAdjunction_homEquiv_symm_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) {G : Sheaf (ProEt.topology R) Ab.{u + 1}}
    {H : Sheaf (ProEt.topology S) Ab.{u + 1}} {K : Sheaf (ProEt.topology T) Ab.{u + 1}}
    (x : G ⟶ (h₂)_*[Ab.{u + 1}].obj H) (y : H ⟶ (h₁)_*[Ab.{u + 1}].obj K) :
    ((upperStarLowerStarAdjunction Ab.{u + 1} (h₁ ≫ h₂)).homEquiv _ _).symm
        (x ≫ (h₂)_*[Ab.{u + 1}].map y ≫ (lowerStarComp Ab.{u + 1} h₁ h₂).hom.app K) =
      (upperStarComp Ab.{u + 1} h₁ h₂).hom.app G ≫
        (h₁)^*[Ab.{u + 1}].map
          (((upperStarLowerStarAdjunction Ab.{u + 1} h₂).homEquiv _ _).symm x) ≫
          ((upperStarLowerStarAdjunction Ab.{u + 1} h₁).homEquiv _ _).symm y := by
  have hc : (lowerStarComp Ab.{u + 1} h₁ h₂).hom = conjugateEquiv
      ((upperStarLowerStarAdjunction Ab.{u + 1} h₂).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} h₁))
      (upperStarLowerStarAdjunction Ab.{u + 1} (h₁ ≫ h₂))
      (upperStarComp Ab.{u + 1} h₁ h₂).hom := by
    simp [upperStarComp, conjugateIsoEquiv]
  have e := homEquiv_symm_comp_conjugateEquiv_app
    ((upperStarLowerStarAdjunction Ab.{u + 1} h₂).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} h₁))
    (upperStarLowerStarAdjunction Ab.{u + 1} (h₁ ≫ h₂)) (upperStarComp Ab.{u + 1} h₁ h₂).hom
    (x ≫ (h₂)_*[Ab.{u + 1}].map y)
  rw [← hc, Category.assoc] at e
  rw [e, Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  erw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm]

/-! ### The sheaves `U ↦ F(Γ(U, 𝒪_U))` -/

variable (F : CommRingCat.{u} ⥤ Ab.{u + 1})

/-- The presheaf `U ↦ F(Γ(U, 𝒪_U))` on the small pro-étale site of `X`. -/
noncomputable def ringSectionsPresheaf (X : Scheme.{u}) : X.ProEtᵒᵖ ⥤ Ab.{u + 1} :=
  (ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ ⋙ F

/-- The projections `V ×_Y X ⟶ V`, natural in `V ∈ Y_proét`. -/
@[simps]
noncomputable def proEtPullbackFst {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ f ⋙ ProEt.forget X ⋙ Over.forget X ⟶
      ProEt.forget Y ⋙ Over.forget Y where
  app V := pullback.fst V.hom f
  naturality V W h := by simp

variable {F}
  (hF : ∀ X : Scheme.{u}, Presheaf.IsSheaf (ProEt.topology X) (ringSectionsPresheaf F X))

/-- The sheaf `U ↦ F(Γ(U, 𝒪_U))` on the small pro-étale site of `X`, given that the presheaves
`AlgebraicGeometry.ProEtale.ringSectionsPresheaf F X` are sheaves. -/
noncomputable abbrev ringSectionsSheaf (X : Scheme.{u}) : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  ⟨ringSectionsPresheaf F X, hF X⟩

/-- The map `F_Y ⟶ f_* F_X` pulling back functions along the projections `V ×_Y X ⟶ V`. -/
noncomputable def toLowerStarRingSectionsSheaf {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ringSectionsSheaf hF Y ⟶ (f)_*[Ab.{u + 1}].obj (ringSectionsSheaf hF X) :=
  ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op (proEtPullbackFst f)) (Scheme.Γ ⋙ F))

/-- The comparison map `φ_f : f^* F_Y ⟶ F_X`, adjoint to the map `F_Y ⟶ f_* F_X` pulling back
functions. -/
noncomputable def upperStarRingSectionsSheafHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)^*[Ab.{u + 1}].obj (ringSectionsSheaf hF Y) ⟶ ringSectionsSheaf hF X :=
  ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
    (toLowerStarRingSectionsSheaf hF f)

/-- Pulling back functions along `V ×_R T ⟶ V` is pulling back along `V ×_R S ⟶ V` and then
along `(V ×_R S) ×_S T ⟶ V ×_R S`. -/
lemma toLowerStarRingSectionsSheaf_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    toLowerStarRingSectionsSheaf hF (h₁ ≫ h₂) =
      toLowerStarRingSectionsSheaf hF h₂ ≫ (h₂)_*[Ab.{u + 1}].map
        (toLowerStarRingSectionsSheaf hF h₁) ≫
          (lowerStarComp Ab.{u + 1} h₁ h₂).hom.app _ := by
  ext V : 3
  have h : ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h₁ h₂).hom.app
      V.unop).left = (pullbackLeftPullbackSndIso V.unop.hom h₂ h₁).inv := by
    simp
  have h' := MorphismProperty.Over.pullbackComp_left_fst_fst (P := @WeaklyEtale) (Q := ⊤) h₁ h₂
    V.unop
  rw [h] at h'
  simp only [toLowerStarRingSectionsSheaf, lowerStarComp,
    Functor.sheafPushforwardContinuousComp', Functor.whiskerRight_app, NatTrans.op_app,
    proEtPullbackFst_app, ObjectProperty.homMk_hom, Functor.comp_map, Iso.trans_hom,
    NatTrans.comp_app]
  simp only [ringSectionsPresheaf, Functor.comp_obj, Functor.op_obj, Over.forget_obj, Γ_obj,
    Functor.id_obj, Functor.const_obj_obj, Γ_map, Quiver.Hom.unop_op,
    Functor.sheafPushforwardContinuousIso_hom, Iso.symm_inv,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj, NatTrans.comp_app,
    Functor.whiskerRight_app, NatTrans.op_app, proEtPullbackFst_app, Functor.comp_map,
    Functor.sheafPushforwardContinuousComp_hom_app_hom_app, Functor.op_map, ProEt.forget_map,
    Over.forget_map, MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id,
    Category.id_comp]
  rw [← h']
  simp only [Scheme.Hom.comp_appTop, Functor.map_comp]
  rfl

/-- **Compatibility of `φ` with composition**: `φ_{h₁ ≫ h₂}` is `φ_{h₁} ∘ h₁^* φ_{h₂}`, up to the
composition isomorphism `(h₁ ≫ h₂)^* ≅ h₁^* h₂^*`. -/
lemma upperStarRingSectionsSheafHom_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    upperStarRingSectionsSheafHom hF (h₁ ≫ h₂) =
      (upperStarComp Ab.{u + 1} h₁ h₂).hom.app _ ≫
        (h₁)^*[Ab.{u + 1}].map (upperStarRingSectionsSheafHom hF h₂) ≫
          upperStarRingSectionsSheafHom hF h₁ := by
  rw [upperStarRingSectionsSheafHom, toLowerStarRingSectionsSheaf_comp,
    upperStarLowerStarAdjunction_homEquiv_symm_comp]
  rfl

/-! ### Weakly étale morphisms -/

/-- For `g : U ⟶ X` weakly étale, the restriction of `F_X` along the localization functor
`U_proét ⥤ X_proét` is `F_U`. -/
noncomputable def localizationRestrictionRingSectionsSheafIso {U X : Scheme.{u}} (g : U ⟶ X)
    [WeaklyEtale g] :
    (localizationRestriction Ab.{u + 1} g inferInstance).obj (ringSectionsSheaf hF X) ≅
      ringSectionsSheaf hF U :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- For `g` weakly étale, the map `F_X ⟶ g_* F_U` is adjoint, for the adjunction between the
restriction along the localization functor and `g_*`, to the identification
`AlgebraicGeometry.ProEtale.localizationRestrictionRingSectionsSheafIso`: the unit
`W ⟶ W ×_X U` of the localization is a section of the projection. -/
lemma localizationRestriction_homEquiv_symm_toLowerStarRingSectionsSheaf {U X : Scheme.{u}}
    (g : U ⟶ X) [WeaklyEtale g] :
    ((localizationRestrictionLowerStarAdjunction Ab.{u + 1} g inferInstance).homEquiv _ _).symm
      (toLowerStarRingSectionsSheaf hF g) =
        (localizationRestrictionRingSectionsSheafIso hF g).hom := by
  ext W : 3
  simp only [localizationRestriction, ringSectionsPresheaf, Functor.comp_obj, Functor.op_obj,
    Over.forget_obj, Γ_obj, localizationRestrictionLowerStarAdjunction,
    toLowerStarRingSectionsSheaf, Adjunction.homEquiv_counit,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app, ObjectProperty.homMk_hom,
    Functor.whiskerRight_app, NatTrans.op_app, proEtPullbackFst_app, Functor.id_obj,
    Functor.const_obj_obj, Functor.comp_map, Γ_map, Quiver.Hom.unop_op,
    Adjunction.sheafPushforwardContinuous_counit_app_hom_app,
    MorphismProperty.Over.mapPullbackAdj_unit_app, Functor.op_map, ProEt.forget_map,
    MorphismProperty.Over.homMk_hom, Over.forget_map, Over.homMk_left,
    localizationRestrictionRingSectionsSheafIso, ObjectProperty.isoMk_hom, Iso.refl_hom,
    NatTrans.id_app]
  rw [← Functor.map_comp, ← Scheme.Hom.comp_appTop]
  erw [pullback.lift_fst]
  simp only [Scheme.Hom.id_appTop]
  exact F.map_id _

/-- **`φ_g` is an isomorphism for `g` weakly étale**: `g^*` is restriction along the localization
functor, under which `φ_g` becomes the identity of `F_U`. -/
lemma isIso_upperStarRingSectionsSheafHom_of_weaklyEtale {U X : Scheme.{u}} (g : U ⟶ X)
    [WeaklyEtale g] : IsIso (upperStarRingSectionsSheafHom hF g) := by
  have h : (upperStarIsoLocalizationRestriction Ab.{u + 1} g inferInstance).inv.app _ ≫
      upperStarRingSectionsSheafHom hF g =
        (localizationRestrictionRingSectionsSheafIso hF g).hom := by
    rw [← localizationRestriction_homEquiv_symm_toLowerStarRingSectionsSheaf,
      upperStarRingSectionsSheafHom, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
      ← NatTrans.naturality_assoc]
    congr 1
    exact Adjunction.leftAdjointUniq_hom_app_counit _ _ _
  have : IsIso ((upperStarIsoLocalizationRestriction Ab.{u + 1} g inferInstance).inv.app _ ≫
      upperStarRingSectionsSheafHom hF g) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((upperStarIsoLocalizationRestriction Ab.{u + 1} g inferInstance).inv.app _) _

/-! ### Naturality in `F` -/

/-- The map of sheaves `F_X ⟶ F'_X` induced by a natural transformation `τ : F ⟶ F'`. -/
noncomputable def ringSectionsSheafMap {F F' : CommRingCat.{u} ⥤ Ab.{u + 1}} (τ : F ⟶ F')
    (hF : ∀ X : Scheme.{u}, Presheaf.IsSheaf (ProEt.topology X) (ringSectionsPresheaf F X))
    (hF' : ∀ X : Scheme.{u}, Presheaf.IsSheaf (ProEt.topology X) (ringSectionsPresheaf F' X))
    (X : Scheme.{u}) : ringSectionsSheaf hF X ⟶ ringSectionsSheaf hF' X :=
  ObjectProperty.homMk (Functor.whiskerLeft ((ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ) τ)

/-- **Naturality of `φ` in `F`**: `φ'_f ∘ f^* τ_Y = τ_X ∘ φ_f` for `τ : F ⟶ F'`. -/
lemma upperStar_map_ringSectionsSheafMap_comp {F F' : CommRingCat.{u} ⥤ Ab.{u + 1}}
    (τ : F ⟶ F')
    (hF : ∀ X : Scheme.{u}, Presheaf.IsSheaf (ProEt.topology X) (ringSectionsPresheaf F X))
    (hF' : ∀ X : Scheme.{u}, Presheaf.IsSheaf (ProEt.topology X) (ringSectionsPresheaf F' X))
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)^*[Ab.{u + 1}].map (ringSectionsSheafMap τ hF hF' Y) ≫
        upperStarRingSectionsSheafHom hF' f =
      upperStarRingSectionsSheafHom hF f ≫ ringSectionsSheafMap τ hF hF' X := by
  rw [upperStarRingSectionsSheafHom, upperStarRingSectionsSheafHom,
    ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  ext V : 3
  exact (τ.naturality _).symm

end AlgebraicGeometry.ProEtale
