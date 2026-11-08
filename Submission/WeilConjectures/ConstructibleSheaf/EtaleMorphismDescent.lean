/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Descent of morphisms of étale sheaves along surjective étale morphisms
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The unit of the adjunction between restriction and pushforward along an étale morphism
restricts sections along the counit of the site adjunction. -/
lemma localizationRestrictionLowerStarAdjunction_unit_app_hom_app' {V X : Scheme.{u}}
    (g : V ⟶ X) (h : Etale g) (P : Sheaf X.smallEtaleTopology A) (U : X.Etaleᵒᵖ) :
    ((localizationRestrictionLowerStarAdjunction A g h).unit.app P).hom.app U =
      P.obj.map
        ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ g h trivial).counit.app U.unop).op :=
  localizationRestrictionLowerStarAdjunction_unit_app_hom_app A g h P U

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
lemma localizationRestriction_obj_obj_map {V X : Scheme.{u}} (g : V ⟶ X) (h : Etale g)
    (P : Sheaf X.smallEtaleTopology A) {U U' : V.Etaleᵒᵖ} (f : U ⟶ U') :
    ((localizationRestriction A g h).obj P).obj.map f =
      P.obj.map ((MorphismProperty.Over.map ⊤ h).map f.unop).op :=
  rfl

section Comp

variable {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)
  [Etale g₁] [Etale g₂] [Etale g₁₂]

/-- The composition isomorphism of the restriction functors along étale morphisms. -/
noncomputable def localizationRestrictionComp' :
    localizationRestriction A g₁₂ inferInstance ≅
      localizationRestriction A g₂ inferInstance ⋙ localizationRestriction A g₁ inferInstance :=
  (Functor.sheafPushforwardContinuousComp' (F := MorphismProperty.Over.map ⊤ (P := @Etale)
      (f := g₁) inferInstance) (G := MorphismProperty.Over.map ⊤ (P := @Etale) (f := g₂)
      inferInstance) (FG := MorphismProperty.Over.map ⊤ (P := @Etale) (f := g₁₂) inferInstance)
    (MorphismProperty.Over.mapComp (Q := ⊤) (P := @Etale) (hf := inferInstance)
      (hg := inferInstance) g₁₂ hg).symm A _ _ _).symm

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
lemma localizationRestrictionComp'_hom_app_hom_app (P : Sheaf R.smallEtaleTopology A)
    (U : T.Etale) :
    ((localizationRestrictionComp' A g₁ g₂ g₁₂ hg).hom.app P).hom.app (op U) =
      P.obj.map ((MorphismProperty.Over.mapComp (Q := ⊤) (P := @Etale) (hf := inferInstance)
        (hg := inferInstance) g₁₂ hg).inv.app U).op := by
  simp [localizationRestrictionComp']

/-- The identification of the pullback along an étale morphism with the restriction is
compatible with the composition isomorphisms. -/
lemma upperStarIsoLocalizationRestriction_comp (P : Sheaf R.smallEtaleTopology A) :
    (upperStarIsoLocalizationRestriction A g₁₂ inferInstance).hom.app P ≫
        (localizationRestrictionComp' A g₁ g₂ g₁₂ hg).hom.app P =
      (upperStarComp A g₁ g₂ g₁₂ hg).hom.app P ≫
        ((g₁)^*[A]).map ((upperStarIsoLocalizationRestriction A g₂ inferInstance).hom.app P) ≫
        (upperStarIsoLocalizationRestriction A g₁ inferInstance).hom.app
          ((localizationRestriction A g₂ inferInstance).obj P) := by
  apply ((upperStarLowerStarAdjunction A g₁₂).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have e₁ := Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction A g₁₂)
    (localizationRestrictionLowerStarAdjunction A g₁₂ inferInstance) P
  have e₂ := Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction A g₂)
    (localizationRestrictionLowerStarAdjunction A g₂ inferInstance) P
  have e₃ := Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction A g₁)
    (localizationRestrictionLowerStarAdjunction A g₁ inferInstance)
    ((localizationRestriction A g₂ inferInstance).obj P)
  have e₄ := (upperStarLowerStarAdjunction A g₁).unit_naturality
    ((upperStarIsoLocalizationRestriction A g₂ inferInstance).hom.app P)
  have e₅ := upperStarComp_hom_app_unit_app A g₁ g₂ P g₁₂ hg
  rw [Adjunction.comp_unit_app] at e₅
  unfold upperStarIsoLocalizationRestriction at e₄ ⊢
  rw [reassoc_of% e₁, reassoc_of% e₅]
  rw [← Functor.map_comp, ← (lowerStarComp A g₁ g₂ g₁₂ hg).hom.naturality, Functor.comp_map,
    ← Functor.map_comp_assoc, (g₁)_*[A].map_comp, reassoc_of% e₄, e₃, (g₂)_*[A].map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% e₂]
  -- both sides are restrictions of sections along morphisms of the small étale site
  ext U : 3
  clear e₁ e₂ e₃ e₄ e₅
  obtain ⟨U⟩ := U
  subst hg
  simp only [Functor.comp_obj, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    localizationRestrictionLowerStarAdjunction_unit_app_hom_app', lowerStar_map_hom_app,
    lowerStarComp_hom_app_hom_app, localizationRestrictionComp'_hom_app_hom_app]
  simp only [localizationRestriction_obj_obj_map, ← Functor.map_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp only [Functor.id_obj, MorphismProperty.Over.mapPullbackAdj_counit_app, op_comp, unop_comp,
    Quiver.Hom.unop_op, MorphismProperty.Comma.comp_hom, MorphismProperty.Over.homMk_hom,
    Comma.comp_left, MorphismProperty.Over.mapComp_inv_app_left, overPullback_obj_left,
    Functor.const_obj_obj, Over.homMk_left, overPullback_obj_hom, Functor.map_comp, Category.assoc,
    MorphismProperty.Over.map_map_left, MorphismProperty.Over.pullbackComp_hom_app_left,
    pullback.map_id, Category.id_comp, pullbackLeftPullbackSndIso_inv_fst]
  exact Category.id_comp (pullback.fst U.hom (g₁ ≫ g₂))

end Comp
section Descent

variable {A} {X' X : Scheme.{u}} (v : X' ⟶ X) [Etale v]

/-- An étale `X`-scheme `W` together with a lift `q` of `W ⟶ X` along `v`, as an étale
`X'`-scheme. -/
noncomputable def liftEtale {W : X.Etale} (q : W ⟶ Scheme.Etale.mk v) : X'.Etale :=
  haveI : Etale (q.left ≫ v) := by
    have hq : q.left ≫ v = W.hom := MorphismProperty.Over.w q
    rw [hq]
    exact W.prop
  haveI : Etale q.left := Etale.of_comp q.left v
  Scheme.Etale.mk q.left

/-- The étale `X`-scheme underlying `liftEtale v q` is `W`. -/
noncomputable def liftEtaleIso {W : X.Etale} (q : W ⟶ Scheme.Etale.mk v) :
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale v)).obj (liftEtale v q) ≅ W :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    have hq : q.left ≫ v = W.hom := MorphismProperty.Over.w q
    simp [liftEtale, hq])

@[simp]
lemma liftEtaleIso_hom_left {W : X.Etale} (q : W ⟶ Scheme.Etale.mk v) :
    (liftEtaleIso v q).hom.left = 𝟙 _ :=
  rfl

@[simp]
lemma liftEtaleIso_inv_left {W : X.Etale} (q : W ⟶ Scheme.Etale.mk v) :
    (liftEtaleIso v q).inv.left = 𝟙 _ :=
  rfl

variable {P Q : Sheaf X.smallEtaleTopology A}
  (ψ : (localizationRestriction A v inferInstance).obj P ⟶
    (localizationRestriction A v inferInstance).obj Q)

end Descent

section PullbackDescent

variable {A} {X' X Z : Scheme.{u}} (v : X' ⟶ X) [Etale v] (p : Z ⟶ X') [Etale p] (w : Z ⟶ X)
  [Etale w] (hw : w = p ≫ v) {P Q : Sheaf X.smallEtaleTopology A}
  (ψ : (localizationRestriction A v inferInstance).obj P ⟶
    (localizationRestriction A v inferInstance).obj Q)

end PullbackDescent

end Etale

end AlgebraicGeometry
