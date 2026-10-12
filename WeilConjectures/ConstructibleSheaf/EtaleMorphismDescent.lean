/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom

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
noncomputable def localizationRestrictionComp :
    localizationRestriction A g₁₂ inferInstance ≅
      localizationRestriction A g₂ inferInstance ⋙ localizationRestriction A g₁ inferInstance :=
  (Functor.sheafPushforwardContinuousComp' (F := MorphismProperty.Over.map ⊤ (P := @Etale)
      (f := g₁) inferInstance) (G := MorphismProperty.Over.map ⊤ (P := @Etale) (f := g₂)
      inferInstance) (FG := MorphismProperty.Over.map ⊤ (P := @Etale) (f := g₁₂) inferInstance)
    (MorphismProperty.Over.mapComp (Q := ⊤) (P := @Etale) (hf := inferInstance)
      (hg := inferInstance) g₁₂ hg).symm A _ _ _).symm

lemma localizationRestrictionComp_hom_app_hom_app (P : Sheaf R.smallEtaleTopology A)
    (U : T.Etale) :
    ((localizationRestrictionComp A g₁ g₂ g₁₂ hg).hom.app P).hom.app (op U) =
      P.obj.map ((MorphismProperty.Over.mapComp (Q := ⊤) (P := @Etale) (hf := inferInstance)
        (hg := inferInstance) g₁₂ hg).inv.app U).op := by
  simp [localizationRestrictionComp]

/-- The identification of the pullback along an étale morphism with the restriction is
compatible with the composition isomorphisms. -/
lemma upperStarIsoLocalizationRestriction_comp (P : Sheaf R.smallEtaleTopology A) :
    (upperStarIsoLocalizationRestriction A g₁₂ inferInstance).hom.app P ≫
        (localizationRestrictionComp A g₁ g₂ g₁₂ hg).hom.app P =
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
  simp [localizationRestrictionLowerStarAdjunction_unit_app_hom_app', lowerStar_map_hom_app,
    lowerStarComp_hom_app_hom_app, localizationRestrictionComp_hom_app_hom_app]
  simp only [localizationRestriction_obj_obj_map, ← Functor.map_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp
  erw [pullbackLeftPullbackSndIso_inv_fst]
  exact Category.id_comp (pullback.fst U.hom (g₁ ≫ g₂))

/-- The inverse form of `AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction_comp`. -/
lemma localizationRestrictionComp_hom_app_eq (P : Sheaf R.smallEtaleTopology A) :
    (localizationRestrictionComp A g₁ g₂ g₁₂ hg).hom.app P =
      (upperStarIsoLocalizationRestriction A g₁₂ inferInstance).inv.app P ≫
        (upperStarComp A g₁ g₂ g₁₂ hg).hom.app P ≫
        ((g₁)^*[A]).map ((upperStarIsoLocalizationRestriction A g₂ inferInstance).hom.app P) ≫
        (upperStarIsoLocalizationRestriction A g₁ inferInstance).hom.app
          ((localizationRestriction A g₂ inferInstance).obj P) := by
  rw [← upperStarIsoLocalizationRestriction_comp, Iso.inv_hom_id_app_assoc]

lemma localizationRestrictionComp_inv_app_eq (P : Sheaf R.smallEtaleTopology A) :
    (localizationRestrictionComp A g₁ g₂ g₁₂ hg).inv.app P =
      (upperStarIsoLocalizationRestriction A g₁ inferInstance).inv.app
          ((localizationRestriction A g₂ inferInstance).obj P) ≫
        ((g₁)^*[A]).map ((upperStarIsoLocalizationRestriction A g₂ inferInstance).inv.app P) ≫
        (upperStarComp A g₁ g₂ g₁₂ hg).inv.app P ≫
        (upperStarIsoLocalizationRestriction A g₁₂ inferInstance).hom.app P := by
  rw [← cancel_epi ((localizationRestrictionComp A g₁ g₂ g₁₂ hg).hom.app P),
    Iso.hom_inv_id_app, localizationRestrictionComp_hom_app_eq]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  simp

end Comp

section Descent

variable {A} {X' X : Scheme.{u}} (v : X' ⟶ X) [Etale v]

/-- An étale `X`-scheme `W` together with a lift `q` of `W ⟶ X` along `v`, as an étale
`X'`-scheme. -/
noncomputable def liftEtale {W : X.Etale} (q : W ⟶ Scheme.Etale.mk v) : X'.Etale :=
  haveI : Etale (q.left ≫ v) := by
    rw [show q.left ≫ v = W.hom from MorphismProperty.Over.w q]
    exact W.prop
  haveI : Etale q.left := Etale.of_comp q.left v
  Scheme.Etale.mk q.left

/-- The étale `X`-scheme underlying `liftEtale v q` is `W`. -/
noncomputable def liftEtaleIso {W : X.Etale} (q : W ⟶ Scheme.Etale.mk v) :
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale v)).obj (liftEtale v q) ≅ W :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by simpa using MorphismProperty.Over.w q)

variable {P Q : Sheaf X.smallEtaleTopology A}
  (ψ : (localizationRestriction A v inferInstance).obj P ⟶
    (localizationRestriction A v inferInstance).obj Q)

/-- The map `P(W) ⟶ Q(W)` induced by a morphism `ψ` of the restrictions of `P` and `Q` to `X'`
and a lift `q` of `W` to `X'`. -/
noncomputable def descentComponent {W : X.Etale} (q : W ⟶ Scheme.Etale.mk v) :
    P.obj.obj (op W) ⟶ Q.obj.obj (op W) :=
  P.obj.map (liftEtaleIso v q).hom.op ≫ ψ.hom.app (op (liftEtale v q)) ≫
    Q.obj.map (liftEtaleIso v q).inv.op

/-- The value of `ψ` at an étale `X'`-scheme `T`, transported along an isomorphism `T ≅ T'`. -/
lemma hom_app_eq_of_iso {T T' : X'.Etale} (k : T ≅ T') :
    ψ.hom.app (op T) = ((localizationRestriction A v inferInstance).obj P).obj.map k.hom.op ≫
      ψ.hom.app (op T') ≫ ((localizationRestriction A v inferInstance).obj Q).obj.map k.inv.op := by
  rw [← ψ.hom.naturality_assoc, ← Functor.map_comp, ← op_comp, Iso.inv_hom_id, op_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

lemma descentComponent_naturality {W₁ W₂ : X.Etale} (g : W₁ ⟶ W₂)
    (q₁ : W₁ ⟶ Scheme.Etale.mk v) (q₂ : W₂ ⟶ Scheme.Etale.mk v) (h : g ≫ q₂ = q₁) :
    P.obj.map g.op ≫ descentComponent v ψ q₁ = descentComponent v ψ q₂ ≫ Q.obj.map g.op := by
  subst h
  let k : liftEtale v (g ≫ q₂) ⟶ liftEtale v q₂ := MorphismProperty.Over.homMk g.left
    (by simp [liftEtale])
  have hk := ψ.hom.naturality k.op
  simp only [localizationRestriction_obj_obj_map, Quiver.Hom.unop_op] at hk
  simp only [descentComponent, Category.assoc]
  have e₁ : (liftEtaleIso v (g ≫ q₂)).hom ≫ g =
      (MorphismProperty.Over.map ⊤ (inferInstance : Etale v)).map k ≫
        (liftEtaleIso v q₂).hom := by
    ext; simp [liftEtaleIso, k]
  have e₂ : (liftEtaleIso v (g ≫ q₂)).inv ≫
      (MorphismProperty.Over.map ⊤ (inferInstance : Etale v)).map k = g ≫ (liftEtaleIso v q₂).inv := by
    ext; simp [liftEtaleIso, k]
  rw [← Functor.map_comp_assoc, ← op_comp, e₁, op_comp, Functor.map_comp_assoc]
  erw [reassoc_of% hk]
  rw [← Functor.map_comp, ← op_comp, e₂, op_comp, Functor.map_comp]
  rfl

/-- **Gluing of morphisms along a surjective étale morphism**, in terms of the restriction
functors: a morphism `ψ` of the restrictions of `P` and `Q` to `X'` whose components at an
étale `X`-scheme `W` do not depend on the chosen lift of `W` to `X'` is the restriction of a
morphism `P ⟶ Q`. -/
lemma exists_localizationRestriction_map_eq (hv : Function.Surjective v.base)
    (hψ : ∀ (W : X.Etale) (q₁ q₂ : W ⟶ Scheme.Etale.mk v),
      descentComponent v ψ q₁ = descentComponent v ψ q₂) :
    ∃ φ : P ⟶ Q, (localizationRestriction A v inferInstance).map φ = ψ := by
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let f₀ : Scheme.Etale.mk v ⟶ T := MorphismProperty.Over.homMk v
  let toT : ∀ U : X.Etale, U ⟶ T := fun U ↦ MorphismProperty.Over.homMk U.hom
  have toT_uniq : ∀ {U : X.Etale} (a : U ⟶ T), a = toT U := fun a ↦
    MorphismProperty.Over.Hom.ext ((Category.comp_id _).symm.trans (MorphismProperty.Over.w a))
  let H := presheafHom P.obj Q.obj
  have hH : Presieve.IsSheaf X.smallEtaleTopology H :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.IsSheaf.hom _ _ Q.property)
  have hS : Sieve.generate (Presieve.singleton f₀) ∈ X.smallEtaleTopology T := by
    rw [mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨x', hx'⟩ := hv x
    exact ⟨_, f₀, ⟨_, 𝟙 _, f₀, Presieve.singleton_self _, Category.id_comp _⟩, x', hx'⟩
  have hT : Presieve.IsSheafFor H (Presieve.singleton f₀) :=
    (Presieve.isSheafFor_iff_generate _).2 (hH _ hS)
  let x : H.obj (op (Scheme.Etale.mk v)) :=
    { app := fun W ↦ descentComponent v ψ W.unop.hom
      naturality := fun W W' g ↦
        descentComponent_naturality v ψ g.unop.left _ _ (CategoryTheory.Over.w g.unop) }
  obtain ⟨y, hy, -⟩ := Presieve.isSheafFor_singleton.1 hT x (fun p₁ p₂ _ ↦ by
    ext W : 2
    exact hψ _ _ _)
  refine ⟨⟨{
      app := fun U ↦ y.app (op (CategoryTheory.Over.mk (toT U.unop)))
      naturality := fun U U' g ↦ ?_ }⟩, ?_⟩
  · have := y.naturality (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (toT U'.unop))
      (V := CategoryTheory.Over.mk (toT U.unop)) g.unop (toT_uniq _).symm).op
    exact this
  · apply Sheaf.hom_ext
    ext ⟨T'⟩ : 2
    let α : (MorphismProperty.Over.map ⊤ (inferInstance : Etale v)).obj T' ⟶
        Scheme.Etale.mk v := MorphismProperty.Over.homMk T'.hom
    have hα : α ≫ f₀ = toT _ := toT_uniq _
    have h₁ := congr_arg (fun z ↦ z.app (op (CategoryTheory.Over.mk α))) hy
    simp only at h₁
    rw [presheafHom_map_app α f₀ _ hα] at h₁
    refine h₁.trans ?_
    change descentComponent v ψ α = _
    have he : (liftEtaleIso v α).hom = 𝟙 _ := by ext; simp [liftEtaleIso]
    have he' : (liftEtaleIso v α).inv = 𝟙 _ := by ext; simp [liftEtaleIso]
    simp only [descentComponent, he, he', op_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id]
    rfl

end Descent

end Etale

end AlgebraicGeometry
