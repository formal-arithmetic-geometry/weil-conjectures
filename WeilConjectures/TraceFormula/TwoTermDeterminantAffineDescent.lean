/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.TraceFormula.AffineTwoTermDeterminantData
import WeilConjectures.AlgebraicGeometry.Descent

/-! # Descent of affine determinant functors

Source: Stacks Project, Perfect Complexes, Tags 0FJX and 0FJY.
-/

@[expose] public section
end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry

private theorem iso_square_inv {C : Type*} [Category C] {L M N P : C}
    (a : L ≅ M) (b : N ≅ P) (f : L ⟶ N) (g : M ⟶ P)
    (h : f ≫ b.hom = a.hom ≫ g) : g ≫ b.inv = a.inv ≫ f := by
  apply (cancel_epi a.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem leftAdjointUniq_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L₁ L₂ : C ⥤ D} {R : D ⥤ C} {F₁ F₂ : D ⥤ E} {G : E ⥤ D}
    (a₁ : L₁ ⊣ R) (a₂ : L₂ ⊣ R) (b₁ : F₁ ⊣ G) (b₂ : F₂ ⊣ G) :
    ((a₁.comp b₁).leftAdjointUniq (a₂.comp b₂)).hom =
      Functor.whiskerRight (a₁.leftAdjointUniq a₂).hom F₁ ≫
        Functor.whiskerLeft L₂ (b₁.leftAdjointUniq b₂).hom := by
  apply (conjugateEquiv (a₂.comp b₂) (a₁.comp b₁)).injective
  rw [← conjugateEquiv_comp (a₂.comp b₂) (a₂.comp b₁) (a₁.comp b₁)]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight]
  simp [Adjunction.leftAdjointUniq]

private theorem leftAdjointUniq_ofNatIsoRight
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    (a.leftAdjointUniq (b.ofNatIsoRight e)).hom =
      (conjugateEquiv b a).symm e.hom := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv, conjugateEquiv,
    Functor.comp_obj, Functor.id_obj,
    Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_counit]

private theorem leftAdjointUniq_rightIso
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G) (e : G ≅ G') :
    ((a.ofNatIsoRight e).leftAdjointUniq (b.ofNatIsoRight e)).hom =
      (a.leftAdjointUniq b).hom := by
  apply NatTrans.ext
  funext X
  apply ((a.ofNatIsoRight e).homEquiv X (F'.obj X)).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

private noncomputable def tensorToPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensorPullback f ≅ pullback f :=
  (tensorPullbackSectionAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)

private theorem tensorToPullback_comp {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (g : Y ⟶ X) :
    (tensorPullbackSectionComp h g).hom ≫
      Functor.whiskerRight (tensorToPullback g).hom (tensorPullback h) ≫
      Functor.whiskerLeft (pullback g) (tensorToPullback h).hom =
        (tensorToPullback (h ≫ g)).hom ≫ (pullbackComp h g).inv := by
  let a := tensorPullbackSectionAdjunction (h ≫ g)
  let b := (tensorPullbackSectionAdjunction g).comp (tensorPullbackSectionAdjunction h)
  let c := (pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction h)
  let e := pushforwardComp h g
  have hc : ((pullbackPushforwardAdjunction (h ≫ g)).leftAdjointUniq
      (c.ofNatIsoRight e)).hom = (pullbackComp h g).inv := by
    rw [leftAdjointUniq_ofNatIsoRight]
    apply (conjugateEquiv c (pullbackPushforwardAdjunction (h ≫ g))).injective
    simp only [Equiv.apply_symm_apply]
    exact (conjugateEquiv_pullbackComp_inv h g).symm
  change (a.leftAdjointUniq (b.ofNatIsoRight e)).hom ≫ _ ≫ _ =
    (a.leftAdjointUniq (pullbackPushforwardAdjunction (h ≫ g))).hom ≫ _
  unfold tensorToPullback
  rw [← leftAdjointUniq_comp, ← leftAdjointUniq_rightIso b c e,
    Adjunction.leftAdjointUniq_trans,
    ← hc, Adjunction.leftAdjointUniq_trans]

private theorem tensorToPullback_transport_comp {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (M : X.Modules) (N : Y.Modules) (P : Z.Modules)
    (a : (tensorPullback f).obj M ⟶ N)
    (b : (tensorPullback g).obj N ⟶ P)
    (c : (tensorPullback (g ≫ f)).obj M ⟶ P)
    (hc : (tensorPullbackSectionComp g f).hom.app M ≫
      (tensorPullback g).map a ≫ b = c) :
    (pullbackComp g f).inv.app M ≫
        (pullback g).map ((tensorToPullback f).inv.app M ≫ a) ≫
        (tensorToPullback g).inv.app N ≫ b =
      (tensorToPullback (g ≫ f)).inv.app M ≫ c := by
  apply (cancel_epi ((tensorToPullback (g ≫ f)).hom.app M)).1
  have ht := congrArg (fun t ↦ t.app M) (tensorToPullback_comp g f)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at ht
  rw [← Category.assoc, ← ht]
  rw [Category.assoc, Category.assoc, ← (tensorToPullback g).hom.naturality_assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  exact hc

private theorem leftAdjointUniq_ofNatIsoRightLeft
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G ≅ G') :
    ((a.ofNatIsoRight e).leftAdjointUniq b).hom =
      (conjugateEquiv b a).symm e.inv := by
  ext M
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv, conjugateEquiv,
    Functor.comp_obj, Functor.id_obj,
    Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_counit]

private theorem tensorToPullback_id (X : Scheme.{u}) :
    (tensorToPullback (𝟙 X)).hom ≫ (pullbackId X).hom =
      (twoTermDeterminantPullbackId X).hom := by
  change ((tensorPullbackSectionAdjunction (𝟙 X)).leftAdjointUniq
    (pullbackPushforwardAdjunction (𝟙 X))).hom ≫ _ =
      (((tensorPullbackSectionAdjunction (𝟙 X)).ofNatIsoRight
        (pushforwardId X)).leftAdjointUniq Adjunction.id).hom
  rw [leftAdjointUniq_ofNatIsoRightLeft]
  apply (conjugateEquiv Adjunction.id (tensorPullbackSectionAdjunction (𝟙 X))).injective
  rw [← conjugateEquiv_comp Adjunction.id (pullbackPushforwardAdjunction (𝟙 X))]
  simp only [Adjunction.leftAdjointUniq, Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv,
    Iso.refl_inv, Equiv.apply_symm_apply]
  exact conjugateEquiv_pullbackId_hom X

@[reassoc]
private theorem pullbackComp_naturality {X Y Z : Scheme.{u}} (f : Y ⟶ X)
    (g : Z ⟶ Y) {M N : X.Modules} (e : M ⟶ N) :
    (pullback g).map ((pullback f).map e) ≫ (pullbackComp g f).hom.app N =
      (pullbackComp g f).hom.app M ≫ (pullback (g ≫ f)).map e :=
  (pullbackComp g f).hom.naturality e

attribute [local irreducible] Scheme.Modules.pullback
  Scheme.Modules.pullbackPushforwardAdjunction

private theorem source_affine_hom_ext {X : Scheme.{u}} {M N : X.Modules}
    (a b : M ⟶ N)
    (h : ∀ U : X.affineOpens, (pullback U.1.ι).map a =
      (pullback U.1.ι).map b) : a = b := by
  apply (bijective_toDescentData_map_of_isOpenImmersion
    (fun U : X.affineOpens ↦ U.1.ι) (by
      simpa only [Scheme.Opens.opensRange_ι] using iSup_affineOpens_eq_top X) M N).1
  exact Pseudofunctor.DescentData.hom_ext h

private theorem source_cover_hom_ext {X : Scheme.{u}} {I : Type*} {U : I → Scheme.{u}}
    (p : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (p i)]
    (hp : ⨆ i, (p i).opensRange = ⊤) {M N : X.Modules} (a b : M ⟶ N)
    (h : ∀ i, (pullback (p i)).map a = (pullback (p i)).map b) : a = b := by
  apply (bijective_toDescentData_map_of_isOpenImmersion p hp M N).1
  exact Pseudofunctor.DescentData.hom_ext h

private theorem affine_factor_cover {X Y : Scheme.{u}} (g : Y ⟶ X) :
    ⨆ (i : Σ U : X.affineOpens, {W : Y.affineOpens // W.1 ≤ g ⁻¹ᵁ U.1}),
      i.2.1.1.ι.opensRange = ⊤ := by
  simp only [Scheme.Opens.opensRange_ι]
  apply top_unique
  intro x _
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show g x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ g ⁻¹ᵁ U from hxU)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, ⟨⟨W, hW⟩, hWU⟩⟩, hxW⟩

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

private theorem affine_pullHom_ext {X₁ X₂ Y : Scheme.{u}}
    {M₁ : X₁.Modules} {M₂ : X₂.Modules} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a b : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂)
    (h : ∀ U : Y.affineOpens,
      pullHom (F := modulesPseudofunctor) a U.1.ι (U.1.ι ≫ f₁) (U.1.ι ≫ f₂) =
      pullHom (F := modulesPseudofunctor) b U.1.ι (U.1.ι ≫ f₁) (U.1.ι ≫ f₂)) : a = b := by
  apply source_affine_hom_ext
  intro U
  change (modulesPseudofunctor.map U.1.ι.op.toLoc).toFunctor.map a =
    (modulesPseudofunctor.map U.1.ι.op.toLoc).toFunctor.map b
  rw [map_eq_pullHom (F := modulesPseudofunctor) a U.1.ι (U.1.ι ≫ f₁) (U.1.ι ≫ f₂) rfl rfl,
    map_eq_pullHom (F := modulesPseudofunctor) b U.1.ι (U.1.ι ≫ f₁) (U.1.ι ≫ f₂) rfl rfl, h U]

private noncomputable def unpull
    {C : Type*} [Category C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {X₁ X₂ Y Z : C} {M₁ : F.obj (.mk (Opposite.op X₁))}
    {M₂ : F.obj (.mk (Opposite.op X₂))} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (g : Z ⟶ Y)
    (a : (F.map (g ≫ f₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (g ≫ f₂).op.toLoc).toFunctor.obj M₂) :
    (F.map g.op.toLoc).toFunctor.obj ((F.map f₁.op.toLoc).toFunctor.obj M₁) ⟶
      (F.map g.op.toLoc).toFunctor.obj ((F.map f₂.op.toLoc).toFunctor.obj M₂) :=
  (F.mapComp' f₁.op.toLoc g.op.toLoc (g ≫ f₁).op.toLoc rfl).inv.toNatTrans.app M₁ ≫ a ≫
    (F.mapComp' f₂.op.toLoc g.op.toLoc (g ≫ f₂).op.toLoc rfl).hom.toNatTrans.app M₂

private theorem pullHom_unpull
    {C : Type*} [Category C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {X₁ X₂ Y Z : C} {M₁ : F.obj (.mk (Opposite.op X₁))}
    {M₂ : F.obj (.mk (Opposite.op X₂))} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (g : Z ⟶ Y)
    (a : (F.map (g ≫ f₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (g ≫ f₂).op.toLoc).toFunctor.obj M₂)
    (b : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (hb : (F.map g.op.toLoc).toFunctor.map b = unpull F f₁ f₂ g a) :
    pullHom (F := F) b g (g ≫ f₁) (g ≫ f₂) = a := by
  dsimp only [pullHom]
  rw [hb]
  dsimp only [unpull]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
    Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]

private theorem unpull_naturality
    {C : Type*} [Category C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {X₁ X₂ Y Z W : C} {M₁ : F.obj (.mk (Opposite.op X₁))}
    {M₂ : F.obj (.mk (Opposite.op X₂))} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (g : Z ⟶ Y) (h : W ⟶ Z)
    (a : (F.map (g ≫ f₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (g ≫ f₂).op.toLoc).toFunctor.obj M₂) :
    pullHom (F := F) (unpull F f₁ f₂ g a) h (h ≫ g) (h ≫ g) =
      unpull F f₁ f₂ (h ≫ g)
        (pullHom (F := F) a h ((h ≫ g) ≫ f₁) ((h ≫ g) ≫ f₂)
          (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm) := by
  dsimp only [pullHom, unpull]
  simp only [Functor.map_comp, Category.assoc]
  have h₁ := F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app
    f₁.op.toLoc g.op.toLoc h.op.toLoc (g ≫ f₁).op.toLoc
    (h ≫ g).op.toLoc ((h ≫ g) ≫ f₁).op.toLoc rfl rfl rfl M₁
  have h₂ := F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app
    f₂.op.toLoc g.op.toLoc h.op.toLoc (g ≫ f₂).op.toLoc
    (h ≫ g).op.toLoc ((h ≫ g) ≫ f₂).op.toLoc rfl rfl (by cat_disch) M₂
  rw [← reassoc_of% h₁, ← h₂]

private theorem pullHom_map
    {C : Type*} [Category C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {X Y Z : C} {M N : F.obj (.mk (Opposite.op X))} (b : M ⟶ N)
    (g : Y ⟶ X) (k : Z ⟶ Y) (q : Z ⟶ X) (hq : k ≫ g = q) :
    pullHom (F := F) ((F.map g.op.toLoc).toFunctor.map b) k q q hq hq =
      (F.map q.op.toLoc).toFunctor.map b := by
  exact F.mapComp'_naturality_2 g.op.toLoc k.op.toLoc q.op.toLoc
    (by rw [← hq]; rfl) b

private theorem map_eq_of_pullHom_eq
    {C : Type*} [Category C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {X₁ X₂ Y Z : C} {M₁ : F.obj (.mk (Opposite.op X₁))}
    {M₂ : F.obj (.mk (Opposite.op X₂))} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a b : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Z ⟶ Y) (q₁ : Z ⟶ X₁) (q₂ : Z ⟶ X₂)
    (h₁ : g ≫ f₁ = q₁) (h₂ : g ≫ f₂ = q₂)
    (h : pullHom (F := F) a g q₁ q₂ h₁ h₂ = pullHom (F := F) b g q₁ q₂ h₁ h₂) :
    (F.map g.op.toLoc).toFunctor.map a = (F.map g.op.toLoc).toFunctor.map b := by
  rw [map_eq_pullHom (F := F) a g q₁ q₂ h₁ h₂,
    map_eq_pullHom (F := F) b g q₁ q₂ h₁ h₂, h]

private theorem pullHom_identity
    {C : Type*} [Category C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {X Y Z : C} {M : F.obj (.mk (Opposite.op X))}
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    pullHom (F := F) (𝟙 ((F.map f.op.toLoc).toFunctor.obj M)) g (g ≫ f) (g ≫ f) =
      𝟙 _ := by
  simp [pullHom]

private theorem pullHom_composition
    {C : Type*} [Category C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {X₁ X₂ X₃ Y Z : C} {M₁ : F.obj (.mk (Opposite.op X₁))}
    {M₂ : F.obj (.mk (Opposite.op X₂))} {M₃ : F.obj (.mk (Opposite.op X₃))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (b : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (g : Z ⟶ Y) :
    pullHom (F := F) (a ≫ b) g (g ≫ f₁) (g ≫ f₃) =
      pullHom (F := F) a g (g ≫ f₁) (g ≫ f₂) ≫
        pullHom (F := F) b g (g ≫ f₂) (g ≫ f₃) := by
  simp [pullHom, Functor.map_comp, Category.assoc]

private theorem compatible_family_lift
    {C : Type*} [Category C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {S : C} {I : Type*} {U : I → C} (p : ∀ i, U i ⟶ S)
    {M N : F.obj (.mk (Opposite.op S))}
    (hfull : Function.Surjective
      ((F.toDescentData p).map : (M ⟶ N) → _))
    (a : ∀ i, (F.map (p i).op.toLoc).toFunctor.obj M ⟶
      (F.map (p i).op.toLoc).toFunctor.obj N)
    (ha : ∀ (Y : C) (q : Y ⟶ S) (i j : I) (f : Y ⟶ U i) (g : Y ⟶ U j)
      (hf : f ≫ p i = q) (hg : g ≫ p j = q),
      pullHom (F := F) (a i) f q q hf hf = pullHom (F := F) (a j) g q q hg hg) :
    ∃ b : M ⟶ N, ∀ i, (F.map (p i).op.toLoc).toFunctor.map b = a i := by
  let ψ : (F.toDescentData p).obj M ⟶ (F.toDescentData p).obj N :=
    Pseudofunctor.DescentData.subtypeCompatibleHomEquiv (F := F) p
      ⟨a, fun i j Z f g _heq ↦
        ha Z.left Z.hom i j f.left g.left (Over.w f) (Over.w g)⟩
  obtain ⟨b, hb⟩ := hfull ψ
  exact ⟨b, fun i ↦ congrArg (fun e ↦ e.hom i) hb⟩

set_option maxHeartbeats 800000 in
-- Elaborating the concrete module pseudofunctor requires the additional heartbeats.
private theorem affine_family_glue {X : Scheme.{u}} {M N : X.Modules}
    (a : ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X),
      (pullback f).obj M ⟶ (pullback f).obj N)
    (ha : ∀ (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y),
      pullHom (F := modulesPseudofunctor) (a Y f) g (g ≫ f) (g ≫ f) = a Z (g ≫ f)) :
    ∃ b : M ⟶ N, ∀ U : X.affineOpens, (pullback U.1.ι).map b = a U U.1.ι := by
  have ha' (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X) (hgf : g ≫ f = gf) :
      pullHom (F := modulesPseudofunctor) (a Y f) g gf gf hgf hgf = a Z gf := by
    subst gf
    exact ha Y Z f g
  let c : ∀ U : X.affineOpens, (pullback U.1.ι).obj M ⟶ (pullback U.1.ι).obj N :=
    fun U ↦ a U U.1.ι
  have hc : ∀ (Y : Scheme.{u}) (q : Y ⟶ X) (U V : X.affineOpens)
      (f : Y ⟶ U.1.toScheme) (g : Y ⟶ V.1.toScheme)
      (hf : f ≫ U.1.ι = q) (hg : g ≫ V.1.ι = q),
      pullHom (F := modulesPseudofunctor) (c U) f q q hf hf =
        pullHom (F := modulesPseudofunctor) (c V) g q q hg hg := by
    intro Y q U V f g hf hg
    apply affine_pullHom_ext (f₁ := q) (f₂ := q)
    intro W
    rw [pullHom_pullHom (F := modulesPseudofunctor),
      pullHom_pullHom (F := modulesPseudofunctor)]
    have hf' : (W.1.ι ≫ f) ≫ U.1.ι = W.1.ι ≫ q := by simp [hf]
    have hg' : (W.1.ι ≫ g) ≫ V.1.ι = W.1.ι ≫ q := by simp [hg]
    exact (ha' U W U.1.ι (W.1.ι ≫ f) (W.1.ι ≫ q) hf').trans
      (ha' V W V.1.ι (W.1.ι ≫ g) (W.1.ι ≫ q) hg').symm
  exact compatible_family_lift modulesPseudofunctor
    (fun U : X.affineOpens ↦ U.1.ι)
    (bijective_toDescentData_map_of_isOpenImmersion
      (fun U : X.affineOpens ↦ U.1.ι) (by
        simpa only [Scheme.Opens.opensRange_ι] using iSup_affineOpens_eq_top X) M N).2 c hc

private theorem affine_family_glue_all {X : Scheme.{u}} {M N : X.Modules}
    (a : ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X),
      (pullback f).obj M ⟶ (pullback f).obj N)
    (ha : ∀ (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y),
      pullHom (F := modulesPseudofunctor) (a Y f) g (g ≫ f) (g ≫ f) = a Z (g ≫ f)) :
    ∃ b : M ⟶ N, ∀ (Y : Scheme.{u}) [IsAffine Y] (g : Y ⟶ X),
      (pullback g).map b = a Y g := by
  obtain ⟨b, hb⟩ := affine_family_glue a ha
  refine ⟨b, fun Y _ g ↦ ?_⟩
  let I := Σ U : X.affineOpens, {W : Y.affineOpens // W.1 ≤ g ⁻¹ᵁ U.1}
  apply source_cover_hom_ext (fun i : I ↦ i.2.1.1.ι) (affine_factor_cover g)
  intro i
  let U := i.1
  let W := i.2.1
  have hr : Set.range (W.1.ι ≫ g) ⊆ Set.range U.1.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact i.2.2 z.2
  let k : W.1.toScheme ⟶ U.1.toScheme := IsOpenImmersion.lift U.1.ι (W.1.ι ≫ g) hr
  have hk : k ≫ U.1.ι = W.1.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  apply map_eq_of_pullHom_eq modulesPseudofunctor _ _ W.1.ι (W.1.ι ≫ g) (W.1.ι ≫ g)
    rfl rfl
  have hh := congrArg (fun t ↦ pullHom (F := modulesPseudofunctor) t k
    (W.1.ι ≫ g) (W.1.ι ≫ g) hk hk) (hb U)
  have hk' : pullHom (F := modulesPseudofunctor) (a U U.1.ι) k
      (W.1.ι ≫ g) (W.1.ι ≫ g) hk hk = a W (W.1.ι ≫ g) := by
    have aux (q : W.1.toScheme ⟶ X) (hq : k ≫ U.1.ι = q) :
        pullHom (F := modulesPseudofunctor) (a U U.1.ι) k q q hq hq = a W q := by
      subst q
      exact ha U W U.1.ι k
    exact aux _ hk
  exact (pullHom_map modulesPseudofunctor b g W.1.ι _ rfl).trans
    (((pullHom_map modulesPseudofunctor b U.1.ι k _ hk).symm.trans hh).trans
      (hk'.trans (ha Y W g W.1.ι).symm))

private structure AffineModuleFamily (X : Scheme.{u}) where
  obj : ∀ (Y : Scheme.{u}) [IsAffine Y], (Y ⟶ X) → Y.Modules
  iso : ∀ {Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ Y) (q : Z ⟶ X) (_hq : g ≫ f = q),
    (pullback g).obj (obj Y f) ≅ obj Z q
  iso_comp : ∀ {Y Z W : Scheme.{u}} [IsAffine Y] [IsAffine Z] [IsAffine W]
    (f : Y ⟶ X) (g : Z ⟶ Y) (h : W ⟶ Z)
    (q : Z ⟶ X) (hq : g ≫ f = q) (r : W ⟶ X) (hr : h ≫ q = r),
    (pullbackComp h g).inv.app (obj Y f) ≫
      (pullback h).map (iso f g q hq).hom ≫ (iso q h r hr).hom =
        (iso f (h ≫ g) r (by simp [hq, hr])).hom
  iso_id : ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X),
    (iso f (𝟙 Y) f (Category.id_comp f)).hom = (pullbackId Y).hom.app (obj Y f)

private noncomputable def AffineModuleFamily.transition {X : Scheme.{u}}
    (F : AffineModuleFamily X) {U V Y : Scheme.{u}}
    [IsAffine U] [IsAffine V] [IsAffine Y]
    (u : U ⟶ X) (v : V ⟶ X) (q : Y ⟶ X)
    (f : Y ⟶ U) (g : Y ⟶ V) (hf : f ≫ u = q) (hg : g ≫ v = q) :
    (pullback f).obj (F.obj U u) ⟶ (pullback g).obj (F.obj V v) :=
  (F.iso u f q hf).hom ≫ (F.iso v g q hg).inv

private theorem AffineModuleFamily.transition_pull {X : Scheme.{u}}
    (F : AffineModuleFamily X) {U V Y Z : Scheme.{u}}
    [IsAffine U] [IsAffine V] [IsAffine Y] [IsAffine Z]
    (u : U ⟶ X) (v : V ⟶ X) (q : Y ⟶ X)
    (f : Y ⟶ U) (g : Y ⟶ V) (hf : f ≫ u = q) (hg : g ≫ v = q) (h : Z ⟶ Y) :
    pullHom (F := modulesPseudofunctor) (F.transition u v q f g hf hg) h (h ≫ f) (h ≫ g) =
      F.transition u v (h ≫ q) (h ≫ f) (h ≫ g) (by simp [hf]) (by simp [hg]) := by
  rw [modulesPseudofunctor_pullHom_eq]
  dsimp only [AffineModuleFamily.transition]
  apply (cancel_mono (F.iso v (h ≫ g) (h ≫ q) (by simp [hg])).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp]
  rw [← F.iso_comp v g h q hg (h ≫ q) rfl]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
  exact F.iso_comp u f h q hf (h ≫ q) rfl

private theorem affine_transition_glue {X₁ X₂ Y : Scheme.{u}}
    {M₁ : X₁.Modules} {M₂ : X₂.Modules} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (a : ∀ (Z : Scheme.{u}) [IsAffine Z] (g : Z ⟶ Y),
      (pullback (g ≫ f₁)).obj M₁ ⟶ (pullback (g ≫ f₂)).obj M₂)
    (ha : ∀ (Z W : Scheme.{u}) [IsAffine Z] [IsAffine W]
      (g : Z ⟶ Y) (h : W ⟶ Z),
      pullHom (F := modulesPseudofunctor) (a Z g) h ((h ≫ g) ≫ f₁) ((h ≫ g) ≫ f₂)
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm = a W (h ≫ g)) :
    ∃ b : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂,
      ∀ (Z : Scheme.{u}) [IsAffine Z] (g : Z ⟶ Y),
        pullHom (F := modulesPseudofunctor) b g (g ≫ f₁) (g ≫ f₂) = a Z g := by
  obtain ⟨b, hb⟩ := affine_family_glue_all
    (fun Z _ g ↦ unpull modulesPseudofunctor f₁ f₂ g (a Z g)) (by
      intro Z W _ _ g h
      rw [unpull_naturality, ha])
  refine ⟨b, fun Z _ g ↦ ?_⟩
  exact pullHom_unpull modulesPseudofunctor f₁ f₂ g (a Z g) b (hb Z g)

private theorem AffineModuleFamily.exists_transition {X : Scheme.{u}}
    (F : AffineModuleFamily X) {U V Y : Scheme.{u}} [IsAffine U] [IsAffine V]
    (u : U ⟶ X) (v : V ⟶ X) (q : Y ⟶ X)
    (f : Y ⟶ U) (g : Y ⟶ V) (hf : f ≫ u = q) (hg : g ≫ v = q) :
    ∃ b : (pullback f).obj (F.obj U u) ⟶ (pullback g).obj (F.obj V v),
      ∀ (Z : Scheme.{u}) [IsAffine Z] (h : Z ⟶ Y),
        pullHom (F := modulesPseudofunctor) b h (h ≫ f) (h ≫ g) =
          F.transition u v (h ≫ q) (h ≫ f) (h ≫ g)
            (by simp [hf]) (by simp [hg]) := by
  apply affine_transition_glue f g
    (fun Z _ h ↦ F.transition u v (h ≫ q) (h ≫ f) (h ≫ g)
      (by simp [hf]) (by simp [hg]))
  intro Z W _ _ h k
  convert! F.transition_pull u v (h ≫ q) (h ≫ f) (h ≫ g)
    (by simp [hf]) (by simp [hg]) k using 1

private noncomputable def AffineModuleFamily.globalTransition {X : Scheme.{u}}
    (F : AffineModuleFamily X) {U V Y : Scheme.{u}} [IsAffine U] [IsAffine V]
    (u : U ⟶ X) (v : V ⟶ X) (q : Y ⟶ X)
    (f : Y ⟶ U) (g : Y ⟶ V) (hf : f ≫ u = q) (hg : g ≫ v = q) :
    (pullback f).obj (F.obj U u) ⟶ (pullback g).obj (F.obj V v) :=
  (F.exists_transition u v q f g hf hg).choose

private theorem AffineModuleFamily.globalTransition_spec {X : Scheme.{u}}
    (F : AffineModuleFamily X) {U V Y : Scheme.{u}} [IsAffine U] [IsAffine V]
    (u : U ⟶ X) (v : V ⟶ X) (q : Y ⟶ X)
    (f : Y ⟶ U) (g : Y ⟶ V) (hf : f ≫ u = q) (hg : g ≫ v = q)
    (Z : Scheme.{u}) [IsAffine Z] (h : Z ⟶ Y) :
    pullHom (F := modulesPseudofunctor) (F.globalTransition u v q f g hf hg) h
      (h ≫ f) (h ≫ g) =
        F.transition u v (h ≫ q) (h ≫ f) (h ≫ g)
          (by simp [hf]) (by simp [hg]) :=
  (F.exists_transition u v q f g hf hg).choose_spec Z h

private theorem AffineModuleFamily.globalTransition_affine {X : Scheme.{u}}
    (F : AffineModuleFamily X) {U V Y : Scheme.{u}}
    [IsAffine U] [IsAffine V] [IsAffine Y]
    (u : U ⟶ X) (v : V ⟶ X) (q : Y ⟶ X)
    (f : Y ⟶ U) (g : Y ⟶ V) (hf : f ≫ u = q) (hg : g ≫ v = q) :
    F.globalTransition u v q f g hf hg = F.transition u v q f g hf hg := by
  apply affine_pullHom_ext
  intro W
  rw [F.globalTransition_spec, F.transition_pull]

private theorem AffineModuleFamily.globalTransition_pull {X : Scheme.{u}}
    (F : AffineModuleFamily X) {U V Y Z : Scheme.{u}} [IsAffine U] [IsAffine V]
    (u : U ⟶ X) (v : V ⟶ X) (q : Y ⟶ X)
    (f : Y ⟶ U) (g : Y ⟶ V) (hf : f ≫ u = q) (hg : g ≫ v = q) (h : Z ⟶ Y) :
    pullHom (F := modulesPseudofunctor) (F.globalTransition u v q f g hf hg)
        h (h ≫ f) (h ≫ g) =
      F.globalTransition u v (h ≫ q) (h ≫ f) (h ≫ g) (by simp [hf]) (by simp [hg]) := by
  apply affine_pullHom_ext (f₁ := h ≫ f) (f₂ := h ≫ g)
  intro W
  exact (pullHom_pullHom (F := modulesPseudofunctor)
    (F.globalTransition u v q f g hf hg) h (h ≫ f) (h ≫ g) W.1.ι
      (W.1.ι ≫ (h ≫ f)) (W.1.ι ≫ (h ≫ g))).trans (by
    convert! (F.globalTransition_spec u v q f g hf hg W (W.1.ι ≫ h)).trans
      (F.globalTransition_spec u v (h ≫ q) (h ≫ f) (h ≫ g)
        (by simp [hf]) (by simp [hg]) W W.1.ι).symm using 1)

private theorem AffineModuleFamily.globalTransition_self {X : Scheme.{u}}
    (F : AffineModuleFamily X) {U Y : Scheme.{u}} [IsAffine U]
    (u : U ⟶ X) (q : Y ⟶ X) (f : Y ⟶ U) (hf : f ≫ u = q) :
    F.globalTransition u u q f f hf hf = 𝟙 _ := by
  apply affine_pullHom_ext
  intro W
  rw [F.globalTransition_spec]
  exact (Iso.hom_inv_id _).trans (pullHom_identity modulesPseudofunctor f W.1.ι).symm

private theorem AffineModuleFamily.globalTransition_comp {X : Scheme.{u}}
    (F : AffineModuleFamily X) {U V W Y : Scheme.{u}}
    [IsAffine U] [IsAffine V] [IsAffine W]
    (u : U ⟶ X) (v : V ⟶ X) (w : W ⟶ X) (q : Y ⟶ X)
    (f : Y ⟶ U) (g : Y ⟶ V) (h : Y ⟶ W)
    (hf : f ≫ u = q) (hg : g ≫ v = q) (hh : h ≫ w = q) :
    F.globalTransition u v q f g hf hg ≫ F.globalTransition v w q g h hg hh =
      F.globalTransition u w q f h hf hh := by
  apply affine_pullHom_ext
  intro T
  rw [pullHom_composition, F.globalTransition_spec, F.globalTransition_spec,
    F.globalTransition_spec]
  dsimp only [AffineModuleFamily.transition]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private noncomputable abbrev AffineModuleFamily.descentDataOn {X : Scheme.{u}}
    (F : AffineModuleFamily X) {I : Type*} {Y : I → Scheme.{u}}
    [∀ i, IsAffine (Y i)] (p : ∀ i, Y i ⟶ X) : modulesPseudofunctor.DescentData p where
  obj i := F.obj (Y i) (p i)
  hom {_} q {_ _} f g hf hg := F.globalTransition _ _ q f g hf hg
  pullHom_hom {_ _} h q q' hq {_ _} f g hf hg hf' hg' hhf hhg := by
    subst q'; subst hf'; subst hg'
    exact F.globalTransition_pull _ _ q f g hf hg h
  hom_self {_} q {_} f hf := F.globalTransition_self _ q f hf
  hom_comp {_} q {_ _ _} f g h hf hg hh :=
    F.globalTransition_comp _ _ _ q f g h hf hg hh

private theorem AffineModuleFamily.descentDataOn_hom {X : Scheme.{u}}
    (F : AffineModuleFamily X) {I : Type*} {Y : I → Scheme.{u}}
    [∀ i, IsAffine (Y i)] (p : ∀ i, Y i ⟶ X) {Z : Scheme.{u}} (q : Z ⟶ X)
    {i j : I} (a : Z ⟶ Y i) (b : Z ⟶ Y j) (ha : a ≫ p i = q) (hb : b ≫ p j = q) :
    (F.descentDataOn p).hom q a b ha hb = F.globalTransition (p i) (p j) q a b ha hb := rfl

private noncomputable abbrev AffineModuleFamily.descentData {X : Scheme.{u}}
    (F : AffineModuleFamily X) :
    modulesPseudofunctor.DescentData (fun U : X.affineOpens ↦ U.1.ι) :=
  F.descentDataOn (fun U : X.affineOpens ↦ U.1.ι)

private noncomputable def AffineModuleFamily.glue {X : Scheme.{u}}
    (F : AffineModuleFamily X) : X.Modules := descentGlue F.descentData

private theorem modules_map_functor {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (modulesPseudofunctor.map f.op.toLoc).toFunctor = pullback f := rfl

private noncomputable def restrictDescentData
    {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {I J : Type*} {X : C} {Y : I → C} {p : ∀ i, Y i ⟶ X}
    (D : F.DescentData p) (α : J → I) : F.DescentData (fun j ↦ p (α j)) where
  obj j := D.obj (α j)
  hom {_} q {_ _} f g hf hg := D.hom q f g hf hg
  pullHom_hom {_ _} h q q' hq {_ _} f g hf hg f' g' hf' hg' :=
    D.pullHom_hom h q q' hq f g hf hg f' g' hf' hg'
  hom_self {_} q {_} f hf := D.hom_self q f hf
  hom_comp {_} q {_ _ _} f g h hf hg hh := D.hom_comp q f g h hf hg hh

private noncomputable def restrictDescentFunctor
    {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {I J : Type*} {X : C} {Y : I → C} (p : ∀ i, Y i ⟶ X) (α : J → I) :
    F.DescentData p ⥤ F.DescentData (fun j ↦ p (α j)) where
  obj D := restrictDescentData F D α
  map e := {
    hom j := e.hom (α j)
    comm {_} q {_ _} a b ha hb := e.comm q a b ha hb }
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem restrictDescentData_toDescentData
    {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {I J : Type*} {X : C} {Y : I → C} (p : ∀ i, Y i ⟶ X) (α : J → I)
    (M : F.obj (.mk (Opposite.op X))) :
    restrictDescentData F ((F.toDescentData p).obj M) α =
      (F.toDescentData (fun j ↦ p (α j))).obj M := rfl

private noncomputable def restrictDescentIso
    {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {I J : Type*} {X : C} {Y : I → C} {p : ∀ i, Y i ⟶ X}
    {M : F.obj (.mk (Opposite.op X))} {D : F.DescentData p}
    (e : (F.toDescentData p).obj M ≅ D) (α : J → I) :
    (F.toDescentData (fun j ↦ p (α j))).obj M ≅ restrictDescentData F D α :=
  (eqToIso (restrictDescentData_toDescentData F p α M)).symm ≪≫
    (restrictDescentFunctor F p α).mapIso e

private abbrev AffineTest (X : Scheme.{u}) :=
  Σ Y : Scheme.{u}, { _f : Y ⟶ X // IsAffine Y }

private instance affineTest_isAffine {X : Scheme.{u}} (i : AffineTest X) :
    IsAffine i.1 := i.2.2

private abbrev affineTestArrow (X : Scheme.{u}) (i : AffineTest X) : i.1 ⟶ X := i.2.1

private theorem affineTest_cover (X : Scheme.{u}) :
    Sieve.ofArrows (fun i : AffineTest X ↦ i.1) (affineTestArrow X) ∈
      Scheme.fpqcTopology X := by
  apply Scheme.fpqcTopology.superset_covering _
    (ofArrows_mem_fpqcTopology_of_isOpenImmersion (fun U : X.affineOpens ↦ U.1.ι)
      (by simpa only [Scheme.Opens.opensRange_ι] using iSup_affineOpens_eq_top X))
  rintro Z g ⟨W, k, _, ⟨U⟩, hk⟩
  refine ⟨_, k, affineTestArrow X ⟨U, U.1.ι, U.2⟩, ?_, hk⟩
  exact Presieve.ofArrows.mk (⟨U, U.1.ι, U.2⟩ : AffineTest X)

private theorem AffineModuleFamily.exists_totalDescentIso {X : Scheme.{u}}
    (F : AffineModuleFamily X)
    (hF : ∀ (Z : Scheme.{u}) [IsAffine Z] (f : Z ⟶ X), (F.obj Z f).IsInvertible) :
    Nonempty ((modulesPseudofunctor.toDescentData (affineTestArrow X)).obj F.glue ≅
      F.descentDataOn (affineTestArrow X)) := by
  let p := affineTestArrow X
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_isQuasicoherent_toDescentData_iso p (affineTest_cover X)
    (F.descentDataOn p) (fun i ↦ by
      change (F.obj i.1 (p i)).IsQuasicoherent
      have := hF i.1 (p i)
      infer_instance)
  let α : X.affineOpens → AffineTest X := fun U ↦ ⟨U, U.1.ι, U.2⟩
  let e₀ : (modulesPseudofunctor.toDescentData (fun U : X.affineOpens ↦ U.1.ι)).obj M ≅
      F.descentData := restrictDescentIso modulesPseudofunctor e α
  have := hM
  have := isIso_toGlue
    (ofArrows_mem_fpqcTopology_of_isOpenImmersion (fun U : X.affineOpens ↦ U.1.ι)
      (by simpa only [Scheme.Opens.opensRange_ι] using iSup_affineOpens_eq_top X)) e₀
  let t : M ≅ F.glue := asIso (toGlue e₀.hom)
  exact ⟨(modulesPseudofunctor.toDescentData p).mapIso t.symm ≪≫ e⟩

private noncomputable def AffineModuleFamily.totalDescentIso {X : Scheme.{u}}
    (F : AffineModuleFamily X)
    (hF : ∀ (Z : Scheme.{u}) [IsAffine Z] (f : Z ⟶ X), (F.obj Z f).IsInvertible) :
    (modulesPseudofunctor.toDescentData (affineTestArrow X)).obj F.glue ≅
      F.descentDataOn (affineTestArrow X) := (F.exists_totalDescentIso hF).some

attribute [local irreducible] descentGlue AffineModuleFamily.glue

attribute [local irreducible] AffineModuleFamily.totalDescentIso

private theorem AffineModuleFamily.glue_invertible {X : Scheme.{u}}
    (F : AffineModuleFamily X)
    (hF : ∀ (Z : Scheme.{u}) [IsAffine Z] (f : Z ⟶ X), (F.obj Z f).IsInvertible) :
    F.glue.IsInvertible := by
  have : SheafOfModules.IsInvertible F.glue :=
    isInvertible_of_toDescentData_iso (affineTestArrow X) (affineTest_cover X)
      (F.descentDataOn (affineTestArrow X)) F.glue ⟨F.totalDescentIso hF⟩ (fun i ↦ by
        change SheafOfModules.IsInvertible (F.obj i.1 (affineTestArrow X i))
        have := hF i.1 (affineTestArrow X i)
        exact IsInvertible.sheafOfModules_isInvertible _)
  exact IsInvertible.of_sheafOfModules _

private noncomputable def AffineModuleFamily.comparison {X Y : Scheme.{u}} [IsAffine Y]
    (F : AffineModuleFamily X)
    (hF : ∀ (Z : Scheme.{u}) [IsAffine Z] (f : Z ⟶ X), (F.obj Z f).IsInvertible)
    (f : Y ⟶ X) : (pullback f).obj F.glue ≅ F.obj Y f :=
  let e := F.totalDescentIso hF
  let i : AffineTest X := ⟨Y, f, inferInstance⟩
  ⟨e.hom.hom i, e.inv.hom i,
    congrArg (fun a ↦ a.hom i) e.hom_inv_id,
    congrArg (fun a ↦ a.hom i) e.inv_hom_id⟩

private theorem pullbackCompOfEq_id {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) :
    pullbackCompOfEq (𝟙 Y) f f (Category.id_comp f) M =
      (pullbackId Y).app ((pullback f).obj M) := by
  apply Iso.ext
  rw [← modulesPseudofunctor_mapComp'_inv_app_eq]
  simpa using modulesPseudofunctor.mapComp'_comp_id_inv_app f.op.toLoc M

private theorem AffineModuleFamily.comparison_congr {X Y : Scheme.{u}} [IsAffine Y]
    (F : AffineModuleFamily X)
    (hF : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (F.obj W f).IsInvertible)
    {p q : Y ⟶ X} (h : p = q) :
    (eqToIso (congrArg (fun k ↦ (pullback k).obj F.glue) h)).hom ≫
        (F.comparison hF q).hom =
      (F.comparison hF p).hom ≫ (eqToIso (congrArg (F.obj Y) h)).hom := by
  subst q
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]

private theorem AffineModuleFamily.comparison_comp {X Y Z : Scheme.{u}}
    [IsAffine Y] [IsAffine Z] (F : AffineModuleFamily X)
    (hF : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (F.obj W f).IsInvertible)
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    (pullbackComp g f).inv.app F.glue ≫
        (pullback g).map (F.comparison hF f).hom ≫
          (F.iso f g (g ≫ f) rfl).hom = (F.comparison hF (g ≫ f)).hom := by
  let e := F.totalDescentIso hF
  have hc := e.hom.comm (i₁ := ⟨Y, f, inferInstance⟩)
    (i₂ := ⟨Z, g ≫ f, inferInstance⟩) (g ≫ f) g (𝟙 Z) rfl (Category.id_comp _)
  rw [modulesPseudofunctor_toDescentData_obj_hom,
    F.descentDataOn_hom, F.globalTransition_affine] at hc
  dsimp only [AffineModuleFamily.transition] at hc
  have hi : F.iso (g ≫ f) (𝟙 Z) (g ≫ f) (Category.id_comp _) =
      (pullbackId Z).app (F.obj Z (g ≫ f)) := Iso.ext (F.iso_id Z (g ≫ f))
  rw [hi, pullbackCompOfEq_id] at hc
  change (pullback g).map (F.comparison hF f).hom ≫
    (F.iso f g (g ≫ f) rfl).hom ≫ (pullbackId Z).inv.app _ =
    ((pullbackCompOfEq g f (g ≫ f) rfl F.glue).hom ≫
      (pullbackId Z).inv.app _) ≫ (pullback (𝟙 Z)).map
        (F.comparison hF (g ≫ f)).hom at hc
  rw [Category.assoc, ← (pullbackId Z).inv.naturality (F.comparison hF (g ≫ f)).hom] at hc
  apply (cancel_mono ((pullbackId Z).inv.app (F.obj Z (g ≫ f)))).1
  apply (cancel_epi ((pullbackComp g f).hom.app F.glue)).1
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, pullbackCompOfEq,
    pullbackCongr, eqToIso_refl, Iso.trans_refl, Iso.app_hom, Iso.trans_hom,
    Iso.refl_hom, Category.comp_id, Functor.id_map, NatTrans.id_app,
    Category.id_comp] using hc

attribute [local irreducible] AffineModuleFamily.comparison

private theorem AffineModuleFamily.comparison_compIso {X Y Z : Scheme.{u}}
    [IsAffine Y] [IsAffine Z] (F : AffineModuleFamily X)
    (hF : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (F.obj W f).IsInvertible)
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    ((pullbackComp g f).symm.app F.glue) ≪≫
        (pullback g).mapIso (F.comparison hF f) ≪≫ F.iso f g (g ≫ f) rfl =
      F.comparison hF (g ≫ f) := by
  apply Iso.ext
  exact F.comparison_comp hF f g

private theorem AffineModuleFamily.exists_map {X : Scheme.{u}}
    (F G : AffineModuleFamily X)
    (hF : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (F.obj W f).IsInvertible)
    (hG : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (G.obj W f).IsInvertible)
    (a : ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X), F.obj Y f ⟶ G.obj Y f)
    (ha : ∀ (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y),
      (pullback g).map (a Y f) ≫ (G.iso f g (g ≫ f) rfl).hom =
        (F.iso f g (g ≫ f) rfl).hom ≫ a Z (g ≫ f)) :
    ∃ b : F.glue ⟶ G.glue, ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X),
      (pullback f).map b = (F.comparison hF f).hom ≫ a Y f ≫
        (G.comparison hG f).inv := by
  apply affine_family_glue_all
  intro Y Z _ _ f g
  rw [modulesPseudofunctor_pullHom_eq]
  rw [← F.comparison_compIso hF f g, ← G.comparison_compIso hG f g]
  simp only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc]
  have hh : (F.iso f g (g ≫ f) rfl).hom ≫ a Z (g ≫ f) ≫
      (G.iso f g (g ≫ f) rfl).inv = (pullback g).map (a Y f) := by
    rw [← Category.assoc, ← ha Y Z f g]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ (pullbackComp g f).inv.app F.glue ≫
      (pullback g).map (F.comparison hF f).hom ≫ k ≫
      (pullback g).map (G.comparison hG f).inv ≫ (pullbackComp g f).hom.app G.glue)
    hh.symm

private noncomputable def AffineModuleFamily.map {X : Scheme.{u}}
    (F G : AffineModuleFamily X)
    (hF : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (F.obj W f).IsInvertible)
    (hG : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (G.obj W f).IsInvertible)
    (a : ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X), F.obj Y f ⟶ G.obj Y f)
    (ha : ∀ (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y),
      (pullback g).map (a Y f) ≫ (G.iso f g (g ≫ f) rfl).hom =
        (F.iso f g (g ≫ f) rfl).hom ≫ a Z (g ≫ f)) : F.glue ⟶ G.glue :=
  (F.exists_map G hF hG a ha).choose

private theorem AffineModuleFamily.map_spec {X : Scheme.{u}}
    (F G : AffineModuleFamily X)
    (hF : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (F.obj W f).IsInvertible)
    (hG : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (G.obj W f).IsInvertible)
    (a : ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X), F.obj Y f ⟶ G.obj Y f)
    (ha : ∀ (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y),
      (pullback g).map (a Y f) ≫ (G.iso f g (g ≫ f) rfl).hom =
        (F.iso f g (g ≫ f) rfl).hom ≫ a Z (g ≫ f))
    (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X) :
    (pullback f).map (F.map G hF hG a ha) =
      (F.comparison hF f).hom ≫ a Y f ≫ (G.comparison hG f).inv :=
  (F.exists_map G hF hG a ha).choose_spec Y f

private noncomputable def AffineModuleFamily.mapIso {X : Scheme.{u}}
    (F G : AffineModuleFamily X)
    (hF : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (F.obj W f).IsInvertible)
    (hG : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (G.obj W f).IsInvertible)
    (a : ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X), F.obj Y f ≅ G.obj Y f)
    (ha : ∀ (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y),
      (pullback g).map (a Y f).hom ≫ (G.iso f g (g ≫ f) rfl).hom =
        (F.iso f g (g ≫ f) rfl).hom ≫ (a Z (g ≫ f)).hom) : F.glue ≅ G.glue := by
  have hai (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y) :
      (pullback g).map (a Y f).inv ≫ (F.iso f g (g ≫ f) rfl).hom =
        (G.iso f g (g ≫ f) rfl).hom ≫ (a Z (g ≫ f)).inv := by
    apply (cancel_epi ((pullback g).map (a Y f).hom)).1
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← Category.assoc _ _ (a Z (g ≫ f)).inv, ha Y Z f g]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨F.map G hF hG (fun Y _ f ↦ (a Y f).hom) ha,
    G.map F hG hF (fun Y _ f ↦ (a Y f).inv) hai, ?_, ?_⟩
  · apply source_affine_hom_ext
    intro U
    simp only [Functor.map_comp, F.map_spec, G.map_spec, CategoryTheory.Functor.map_id,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id]
  · apply source_affine_hom_ext
    intro U
    simp only [Functor.map_comp, F.map_spec, G.map_spec, CategoryTheory.Functor.map_id,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]

private theorem AffineModuleFamily.mapIso_hom {X : Scheme.{u}}
    (F G : AffineModuleFamily X)
    (hF : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (F.obj W f).IsInvertible)
    (hG : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (G.obj W f).IsInvertible)
    (a : ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X), F.obj Y f ≅ G.obj Y f)
    (ha : ∀ (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y),
      (pullback g).map (a Y f).hom ≫ (G.iso f g (g ≫ f) rfl).hom =
        (F.iso f g (g ≫ f) rfl).hom ≫ (a Z (g ≫ f)).hom) :
    (F.mapIso G hF hG a ha).hom = F.map G hF hG (fun Y _ f ↦ (a Y f).hom) ha := rfl

attribute [local irreducible] AffineModuleFamily.mapIso

private noncomputable def affine_family_glue_iso {X : Scheme.{u}} {M N : X.Modules}
    (a : ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X),
      (pullback f).obj M ≅ (pullback f).obj N)
    (ha : ∀ (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y),
      (pullbackComp g f).symm.app M ≪≫ (pullback g).mapIso (a Y f) ≪≫
        (pullbackComp g f).app N = a Z (g ≫ f)) : M ≅ N := by
  have hh (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y) :
      pullHom (F := modulesPseudofunctor) (a Y f).hom g (g ≫ f) (g ≫ f) =
        (a Z (g ≫ f)).hom := by
    rw [modulesPseudofunctor_pullHom_eq]
    exact congrArg Iso.hom (ha Y Z f g)
  have hi (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y) :
      pullHom (F := modulesPseudofunctor) (a Y f).inv g (g ≫ f) (g ≫ f) =
        (a Z (g ≫ f)).inv := by
    rw [modulesPseudofunctor_pullHom_eq]
    have h := congrArg Iso.inv (ha Y Z f g)
    simpa only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Iso.symm_hom,
      Functor.mapIso_inv, Category.assoc] using h
  let b := (affine_family_glue_all (fun Y _ f ↦ (a Y f).hom) hh).choose
  have hb := (affine_family_glue_all (fun Y _ f ↦ (a Y f).hom) hh).choose_spec
  let c := (affine_family_glue_all (fun Y _ f ↦ (a Y f).inv) hi).choose
  have hc := (affine_family_glue_all (fun Y _ f ↦ (a Y f).inv) hi).choose_spec
  refine ⟨b, c, ?_, ?_⟩
  · apply source_affine_hom_ext
    intro U
    rw [Functor.map_comp, hb, hc, CategoryTheory.Functor.map_id, Iso.hom_inv_id]
  · apply source_affine_hom_ext
    intro U
    rw [Functor.map_comp, hc, hb, CategoryTheory.Functor.map_id, Iso.inv_hom_id]

private theorem affine_family_glue_iso_spec {X : Scheme.{u}} {M N : X.Modules}
    (a : ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X),
      (pullback f).obj M ≅ (pullback f).obj N)
    (ha : ∀ (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y),
      (pullbackComp g f).symm.app M ≪≫ (pullback g).mapIso (a Y f) ≪≫
        (pullbackComp g f).app N = a Z (g ≫ f))
    (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X) :
    (pullback f).map (affine_family_glue_iso a ha).hom = (a Y f).hom :=
  (affine_family_glue_all (fun Y _ f ↦ (a Y f).hom)
    (fun Y Z _ _ f g ↦ by
      rw [modulesPseudofunctor_pullHom_eq]
      exact congrArg Iso.hom (ha Y Z f g))).choose_spec Y f

private theorem pullback_comp_assoc {X Y Z W : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (h : W ⟶ Z) (M : X.Modules) :
    (pullback h).map ((pullbackComp g f).inv.app M) ≫
        (pullbackComp h g).hom.app ((pullback f).obj M) =
      (pullbackComp h (g ≫ f)).hom.app M ≫
        (pullbackCompOfEq (h ≫ g) f (h ≫ g ≫ f) (Category.assoc h g f) M).inv := by
  have hc := modulesPseudofunctor.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app
    f.op.toLoc g.op.toLoc h.op.toLoc (g ≫ f).op.toLoc (h ≫ g).op.toLoc
    (h ≫ g ≫ f).op.toLoc rfl rfl rfl M
  rw [modulesPseudofunctor_mapComp'_inv_app_eq f (h ≫ g) (h ≫ g ≫ f)
      (Category.assoc h g f) M,
    modulesPseudofunctor_mapComp'_hom_app_eq (g ≫ f) h (h ≫ g ≫ f) rfl M,
    modulesPseudofunctor_mapComp'_hom_app_eq g h (h ≫ g) rfl,
    modulesPseudofunctor_mapComp'_inv_app_eq f g (g ≫ f) rfl M] at hc
  have hi : (pullback h).mapIso ((pullbackComp g f).symm.app M) ≪≫
      (pullbackComp h g).app ((pullback f).obj M) =
    (pullbackComp h (g ≫ f)).app M ≪≫
      (pullbackCompOfEq (h ≫ g) f (h ≫ g ≫ f) (Category.assoc h g f) M).symm := by
    apply Iso.ext_inv
    simpa only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Functor.mapIso_inv,
      modules_map_functor, pullbackCompOfEq, pullbackCongr, eqToIso_refl,
      Iso.trans_refl, Iso.app_hom, Iso.trans_hom, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Category.id_comp, Category.comp_id] using hc.symm
  exact congrArg Iso.hom hi

private theorem pullback_comp_assoc_iso {X Y Z W : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (h : W ⟶ Z) (M : X.Modules) :
    (pullbackComp h g).symm.app ((pullback f).obj M) ≪≫
        (pullback h).mapIso ((pullbackComp g f).app M) ≪≫
        (pullbackComp h (g ≫ f)).app M =
      pullbackCompOfEq (h ≫ g) f (h ≫ g ≫ f) (Category.assoc h g f) M := by
  apply Iso.ext
  apply (cancel_epi ((pullbackComp h g).hom.app ((pullback f).obj M))).1
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.hom_inv_id_app_assoc]
  apply (cancel_epi ((pullback h).map ((pullbackComp g f).inv.app M))).1
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have hh := congrArg (fun k ↦ k ≫
    (pullbackCompOfEq (h ≫ g) f (h ≫ g ≫ f) (Category.assoc h g f) M).hom)
    (pullback_comp_assoc f g h M)
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh.symm

private theorem AffineModuleFamily.comparison_congrIso {X Y : Scheme.{u}} [IsAffine Y]
    (F : AffineModuleFamily X)
    (hF : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (F.obj W f).IsInvertible)
    {p q : Y ⟶ X} (h : p = q) :
    F.comparison hF p ≪≫ eqToIso (congrArg (F.obj Y) h) =
      (pullbackCongr h).app F.glue ≪≫ F.comparison hF q := by
  subst q
  apply Iso.ext
  simp only [pullbackCongr, eqToIso_refl, Iso.trans_hom, Iso.app_hom,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.comp_id]

private noncomputable def AffineModuleFamily.fromModuleIso {X : Scheme.{u}}
    (F : AffineModuleFamily X)
    (hF : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (F.obj W f).IsInvertible)
    (M : X.Modules)
    (a : ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X), (pullback f).obj M ≅ F.obj Y f)
    (ha : ∀ (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y),
      (pullbackComp g f).inv.app M ≫ (pullback g).map (a Y f).hom ≫
        (F.iso f g (g ≫ f) rfl).hom = (a Z (g ≫ f)).hom) : M ≅ F.glue :=
  affine_family_glue_iso (fun Y _ f ↦ a Y f ≪≫ (F.comparison hF f).symm) (by
    intro Y Z _ _ f g
    have he : (pullbackComp g f).symm.app M ≪≫ (pullback g).mapIso (a Y f) ≪≫
        F.iso f g (g ≫ f) rfl = a Z (g ≫ f) := Iso.ext (ha Y Z f g)
    rw [← F.comparison_compIso hF f g, ← he]
    apply Iso.ext
    simp only [Functor.mapIso_trans, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      Category.assoc, Iso.hom_inv_id_assoc]
)

private theorem AffineModuleFamily.fromModuleIso_spec {X Y : Scheme.{u}} [IsAffine Y]
    (F : AffineModuleFamily X)
    (hF : ∀ (W : Scheme.{u}) [IsAffine W] (f : W ⟶ X), (F.obj W f).IsInvertible)
    (M : X.Modules)
    (a : ∀ (Z : Scheme.{u}) [IsAffine Z] (f : Z ⟶ X), (pullback f).obj M ≅ F.obj Z f)
    (ha : ∀ (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y),
      (pullbackComp g f).inv.app M ≫ (pullback g).map (a Y f).hom ≫
        (F.iso f g (g ≫ f) rfl).hom = (a Z (g ≫ f)).hom)
    (f : Y ⟶ X) : (pullback f).map (F.fromModuleIso hF M a ha).hom =
      (a Y f).hom ≫ (F.comparison hF f).inv :=
  affine_family_glue_iso_spec _ _ Y f

attribute [local irreducible] affine_family_glue_iso AffineModuleFamily.fromModuleIso

private noncomputable abbrev rawAbelian (T : Type u) [TopologicalSpace T]
    (R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}) :
    Abelian (SheafOfModules.{u} R) := inferInstance
attribute [local instance 100000] rawAbelian

private noncomputable abbrev restrictionAbelian (T : Type u) [TopologicalSpace T]
    (R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}) (U : TopologicalSpace.Opens T) :
    Abelian (SheafOfModules.{u} (R.over U)) := inferInstance
attribute [local instance 100000] restrictionAbelian

-- The two universes intentionally match the derived-category assumptions.
set_option linter.checkUnivs false in
private abbrev SchemeDerivedInstances := ∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))

set_option linter.checkUnivs false in
private abbrev RestrictionDerivedInstances := ∀ (X : Scheme.{u}) (U : X.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))

section AffineDeterminants

variable [d : SchemeDerivedInstances.{u, w}] [dr : RestrictionDerivedInstances.{u, w}]
    (κ : TwoTermDeterminantPullbackCoherence.{u, w}) (A : AffineTwoTermDeterminantData κ)

omit dr in
private theorem determinantIso_refl {X : Scheme.{u}}
    (F : TwoTermPerfectCore X ⥤ Core X.Modules)
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) :
    (twoTermDeterminantIso F hL hL (Iso.refl L)).hom = 𝟙 _ := by
  change (F ⋙ Core.inclusion X.Modules).map
    (𝟙 (Core.mk (⟨L, hL⟩ : (isTwoTermPerfect X).FullSubcategory))) = _
  exact (F ⋙ Core.inclusion X.Modules).map_id _

omit dr in
private theorem determinantIso_trans {X : Scheme.{u}}
    (F : TwoTermPerfectCore X ⥤ Core X.Modules)
    {L M N : schemeDerivedCategory X} (hL : isTwoTermPerfect X L)
    (hM : isTwoTermPerfect X M) (hN : isTwoTermPerfect X N) (e : L ≅ M) (f : M ≅ N) :
    (twoTermDeterminantIso F hL hN (e ≪≫ f)).hom =
      (twoTermDeterminantIso F hL hM e).hom ≫ (twoTermDeterminantIso F hM hN f).hom := by
  let x : TwoTermPerfectCore X := Core.mk ⟨L, hL⟩
  let y : TwoTermPerfectCore X := Core.mk ⟨M, hM⟩
  let z : TwoTermPerfectCore X := Core.mk ⟨N, hN⟩
  change (F ⋙ Core.inclusion X.Modules).map
    ((CoreHom.mk ((isTwoTermPerfect X).isoMk e) : x ⟶ y) ≫
      (CoreHom.mk ((isTwoTermPerfect X).isoMk f) : y ⟶ z)) = _
  exact (F ⋙ Core.inclusion X.Modules).map_comp _ _

private noncomputable def ordinaryAffinePullback {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (g : Y ⟶ X) (L : schemeDerivedCategory X)
    (hL : isTwoTermPerfect X L) :
    (pullback g).obj (twoTermDeterminantValue (A.functor X) L hL) ≅
      twoTermDeterminantValue (A.functor Y) ((derivedPullback g).obj L)
        (twoTermPerfect_pullback g L hL) :=
  (tensorToPullback g).symm.app _ ≪≫ A.pullbackIso g L hL

@[reassoc]
private theorem ordinaryAffinePullback_naturality {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (g : Y ⟶ X) {L M : schemeDerivedCategory X}
    (hL : isTwoTermPerfect X L) (hM : isTwoTermPerfect X M) (e : L ≅ M) :
    (pullback g).map (twoTermDeterminantIso (A.functor X) hL hM e).hom ≫
        (ordinaryAffinePullback κ A g M hM).hom =
      (ordinaryAffinePullback κ A g L hL).hom ≫
        (twoTermDeterminantIso (A.functor Y) (twoTermPerfect_pullback g L hL)
          (twoTermPerfect_pullback g M hM) ((derivedPullback g).mapIso e)).hom := by
  dsimp only [ordinaryAffinePullback, Iso.trans_hom, Iso.app_hom, Iso.symm_hom]
  rw [← Category.assoc, (tensorToPullback g).inv.naturality,
    Category.assoc, A.pullback_naturality]
  simp only [Category.assoc]

private theorem ordinaryAffinePullback_id (X : Scheme.{u}) [IsAffine X]
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) :
    (ordinaryAffinePullback κ A (𝟙 X) L hL).hom ≫
        (twoTermDeterminantIso (A.functor X) (twoTermPerfect_pullback (𝟙 X) L hL) hL
          ((κ.derivedId X).app L)).hom =
      (pullbackId X).hom.app (twoTermDeterminantValue (A.functor X) L hL) := by
  dsimp only [ordinaryAffinePullback, Iso.trans_hom, Iso.app_hom, Iso.symm_hom]
  rw [Category.assoc, A.pullback_id]
  have hi := congrArg (fun t ↦ t.app (twoTermDeterminantValue (A.functor X) L hL))
    (tensorToPullback_id X)
  dsimp only [NatTrans.comp_app] at hi
  rw [← hi]
  simp only [Iso.inv_hom_id_app_assoc]

private theorem ordinaryAffinePullback_comp {X Y Z : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsAffine Z] (g : Y ⟶ X) (h : Z ⟶ Y)
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) :
    (pullbackComp h g).inv.app (twoTermDeterminantValue (A.functor X) L hL) ≫
        (pullback h).map (ordinaryAffinePullback κ A g L hL).hom ≫
        (ordinaryAffinePullback κ A h ((derivedPullback g).obj L)
          (twoTermPerfect_pullback g L hL)).hom ≫
        (twoTermDeterminantIso (A.functor Z)
          (twoTermPerfect_pullback h _ (twoTermPerfect_pullback g L hL))
          (twoTermPerfect_pullback (h ≫ g) L hL) ((κ.derivedComp h g).app L)).hom =
      (ordinaryAffinePullback κ A (h ≫ g) L hL).hom := by
  let c := (twoTermDeterminantIso (A.functor Z)
    (twoTermPerfect_pullback h _ (twoTermPerfect_pullback g L hL))
    (twoTermPerfect_pullback (h ≫ g) L hL) ((κ.derivedComp h g).app L)).hom
  simpa only [ordinaryAffinePullback, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Category.assoc] using tensorToPullback_transport_comp g h _ _ _
    (A.pullbackIso g L hL).hom
    ((A.pullbackIso h ((derivedPullback g).obj L) (twoTermPerfect_pullback g L hL)).hom ≫ c)
    (A.pullbackIso (h ≫ g) L hL).hom (A.pullback_comp g h L hL)

private noncomputable abbrev affineDeterminantValue {X : Scheme.{u}}
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L)
    (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X) : Y.Modules :=
  twoTermDeterminantValue (A.functor Y) ((derivedPullback f).obj L)
    (twoTermPerfect_pullback f L hL)

private noncomputable def affineDeterminantComparison {X Y Z : Scheme.{u}}
    [IsAffine Y] [IsAffine Z] (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L)
    (f : Y ⟶ X) (g : Z ⟶ Y) (q : Z ⟶ X) (hq : g ≫ f = q) :
    (pullback g).obj (affineDeterminantValue κ A L hL Y f) ≅
      affineDeterminantValue κ A L hL Z q :=
  (tensorToPullback g).symm.app _ ≪≫
    A.pullbackIso g ((derivedPullback f).obj L) (twoTermPerfect_pullback f L hL) ≪≫
      twoTermDeterminantIso (A.functor Z)
        (twoTermPerfect_pullback g _ (twoTermPerfect_pullback f L hL))
        (twoTermPerfect_pullback q L hL)
        ((κ.derivedComp g f).app L ≪≫
          eqToIso (congrArg (fun k : Z ⟶ X ↦ (derivedPullback k).obj L) hq))

private theorem affineDeterminantComparison_eq {X Y Z : Scheme.{u}}
    [IsAffine Y] [IsAffine Z] (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L)
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    affineDeterminantComparison κ A L hL f g (g ≫ f) rfl =
      ordinaryAffinePullback κ A g ((derivedPullback f).obj L)
        (twoTermPerfect_pullback f L hL) ≪≫
        twoTermDeterminantIso (A.functor Z)
          (twoTermPerfect_pullback g _ (twoTermPerfect_pullback f L hL))
          (twoTermPerfect_pullback (g ≫ f) L hL) ((κ.derivedComp g f).app L) := by
  dsimp only [affineDeterminantComparison]
  rw [eqToIso_refl, Iso.trans_refl]
  rfl

private theorem affineDeterminantComparison_naturality {X Y Z : Scheme.{u}}
    [IsAffine Y] [IsAffine Z] {L M : schemeDerivedCategory X}
    (hL : isTwoTermPerfect X L) (hM : isTwoTermPerfect X M) (e : L ≅ M)
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    (pullback g).map
        (twoTermDeterminantIso (A.functor Y) (twoTermPerfect_pullback f L hL)
          (twoTermPerfect_pullback f M hM) ((derivedPullback f).mapIso e)).hom ≫
        (affineDeterminantComparison κ A M hM f g (g ≫ f) rfl).hom =
      (affineDeterminantComparison κ A L hL f g (g ≫ f) rfl).hom ≫
        (twoTermDeterminantIso (A.functor Z) (twoTermPerfect_pullback (g ≫ f) L hL)
          (twoTermPerfect_pullback (g ≫ f) M hM) ((derivedPullback (g ≫ f)).mapIso e)).hom := by
  have he : (derivedPullback g).mapIso ((derivedPullback f).mapIso e) ≪≫
        (κ.derivedComp g f).app M =
      (κ.derivedComp g f).app L ≪≫ (derivedPullback (g ≫ f)).mapIso e := by
    apply Iso.ext
    exact (κ.derivedComp g f).hom.naturality e.hom
  have hd := congrArg (fun t ↦
    (twoTermDeterminantIso (A.functor Z)
      (twoTermPerfect_pullback g _ (twoTermPerfect_pullback f L hL))
      (twoTermPerfect_pullback (g ≫ f) M hM) t).hom) he
  rw [determinantIso_trans (hM := twoTermPerfect_pullback g _
    (twoTermPerfect_pullback f M hM)),
    determinantIso_trans (hM := twoTermPerfect_pullback (g ≫ f) L hL)] at hd
  dsimp only [affineDeterminantComparison]
  simp only [eqToIso_refl, Iso.trans_refl, Iso.trans_hom, Iso.app_hom, Iso.symm_hom]
  rw [(tensorToPullback g).inv.naturality_assoc]
  have hp := A.pullback_naturality g (twoTermPerfect_pullback f L hL)
    (twoTermPerfect_pullback f M hM) ((derivedPullback f).mapIso e)
  rw [← Category.assoc ((tensorPullback g).map
    (twoTermDeterminantIso (A.functor Y) _ _ ((derivedPullback f).mapIso e)).hom)
    (A.pullbackIso g ((derivedPullback f).obj M) _).hom, hp]
  simp only [Category.assoc]
  rw [hd]

private theorem affineDeterminantComparison_id {X Y : Scheme.{u}} [IsAffine Y]
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) (f : Y ⟶ X) :
    (affineDeterminantComparison κ A L hL f (𝟙 Y) f (Category.id_comp f)).hom =
      (pullbackId Y).hom.app (affineDeterminantValue κ A L hL Y f) := by
  have hu : (κ.derivedComp (𝟙 Y) f).app L ≪≫
        eqToIso (congrArg (fun k : Y ⟶ X ↦ (derivedPullback k).obj L)
          (Category.id_comp f)) = (κ.derivedId Y).app ((derivedPullback f).obj L) := by
    apply Iso.ext
    simpa [eqToHom_app] using congrArg (fun t ↦ t.hom.app L) (κ.left_unit f)
  change ((ordinaryAffinePullback κ A (𝟙 Y) ((derivedPullback f).obj L)
    (twoTermPerfect_pullback f L hL)) ≪≫ _).hom = _
  rw [hu]
  exact ordinaryAffinePullback_id κ A Y _ _

private noncomputable abbrev derivedDeterminantComp {X Y Z : Scheme.{u}}
    [IsAffine Z] (g : Z ⟶ Y) (f : Y ⟶ X)
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) :=
  twoTermDeterminantIso (A.functor Z)
    (twoTermPerfect_pullback g _ (twoTermPerfect_pullback f L hL))
    (twoTermPerfect_pullback (g ≫ f) L hL) ((κ.derivedComp g f).app L)

omit dr in
private theorem derived_comp_assoc {X Y Z W : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (h : W ⟶ Z) (L : schemeDerivedCategory X) :
    (derivedPullback h).mapIso ((κ.derivedComp g f).app L) ≪≫
        (κ.derivedComp h (g ≫ f)).app L =
      (κ.derivedComp h g).app ((derivedPullback f).obj L) ≪≫
        (κ.derivedComp (h ≫ g) f).app L ≪≫
          eqToIso (congrArg (fun k : W ⟶ X ↦ (derivedPullback k).obj L)
            (Category.assoc h g f)) := by
  apply Iso.ext
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Iso.app_hom, Functor.mapIso_hom,
    Functor.comp_obj, eqToIso.hom, eqToHom_app]
    using congrArg (fun t ↦ t.hom.app L) (κ.associativity h g f)

private theorem affineDeterminantComparison_comp {X Y Z W : Scheme.{u}}
    [IsAffine Y] [IsAffine Z] [IsAffine W]
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L)
    (f : Y ⟶ X) (g : Z ⟶ Y) (h : W ⟶ Z) (q : Z ⟶ X) (hq : g ≫ f = q)
    (r : W ⟶ X) (hr : h ≫ q = r) :
    (pullbackComp h g).inv.app (affineDeterminantValue κ A L hL Y f) ≫
        (pullback h).map (affineDeterminantComparison κ A L hL f g q hq).hom ≫
          (affineDeterminantComparison κ A L hL q h r hr).hom =
      (affineDeterminantComparison κ A L hL f (h ≫ g) r
        (by simp [Category.assoc, hq, hr])).hom := by
  subst q
  subst r
  have hc := derived_comp_assoc κ f g h L
  have hd := congrArg (fun t ↦ (twoTermDeterminantIso (A.functor W)
    (twoTermPerfect_pullback h _ (twoTermPerfect_pullback g _
      (twoTermPerfect_pullback f L hL)))
    (twoTermPerfect_pullback (h ≫ g ≫ f) L hL) t).hom) hc
  rw [determinantIso_trans (hM := twoTermPerfect_pullback h _
    (twoTermPerfect_pullback (g ≫ f) L hL)),
    determinantIso_trans (hM := twoTermPerfect_pullback (h ≫ g) _
      (twoTermPerfect_pullback f L hL))] at hd
  rw [affineDeterminantComparison_eq, affineDeterminantComparison_eq]
  change (pullbackComp h g).inv.app _ ≫
      (pullback h).map ((ordinaryAffinePullback κ A g _ _).hom ≫
        (twoTermDeterminantIso (A.functor Z)
          (twoTermPerfect_pullback g _ (twoTermPerfect_pullback f L hL))
          (twoTermPerfect_pullback (g ≫ f) L hL) ((κ.derivedComp g f).app L)).hom) ≫
      (ordinaryAffinePullback κ A h _ _).hom ≫
        (twoTermDeterminantIso (A.functor W)
          (twoTermPerfect_pullback h _ (twoTermPerfect_pullback (g ≫ f) L hL))
          (twoTermPerfect_pullback (h ≫ g ≫ f) L hL)
          ((κ.derivedComp h (g ≫ f)).app L)).hom =
    (ordinaryAffinePullback κ A (h ≫ g) _ _).hom ≫
      (twoTermDeterminantIso (A.functor W)
        (twoTermPerfect_pullback (h ≫ g) _ (twoTermPerfect_pullback f L hL))
        (twoTermPerfect_pullback (h ≫ g ≫ f) L hL)
        ((κ.derivedComp (h ≫ g) f).app L ≪≫
          eqToIso (congrArg (fun k : W ⟶ X ↦ (derivedPullback k).obj L)
            (Category.assoc h g f)))).hom
  simp only [Functor.map_comp, Category.assoc]
  rw [ordinaryAffinePullback_naturality_assoc]
  rw [hd]
  apply (cancel_mono (twoTermDeterminantIso (A.functor W)
    (twoTermPerfect_pullback (h ≫ g) _ (twoTermPerfect_pullback f L hL))
    (twoTermPerfect_pullback (h ≫ g ≫ f) L hL)
    ((κ.derivedComp (h ≫ g) f).app L ≪≫
      eqToIso (congrArg (fun k : W ⟶ X ↦ (derivedPullback k).obj L)
        (Category.assoc h g f)))).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact ordinaryAffinePullback_comp κ A g h ((derivedPullback f).obj L)
    (twoTermPerfect_pullback f L hL)

private noncomputable def affineDeterminantFamily {X : Scheme.{u}}
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) : AffineModuleFamily X where
  obj := affineDeterminantValue κ A L hL
  iso := affineDeterminantComparison κ A L hL
  iso_comp := affineDeterminantComparison_comp κ A L hL
  iso_id := fun _ _ f ↦ affineDeterminantComparison_id κ A L hL f

private theorem affineDeterminantFamily_invertible {X : Scheme.{u}}
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L)
    (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X) :
    ((affineDeterminantFamily κ A L hL).obj Y f).IsInvertible :=
  A.invertible Y _ (twoTermPerfect_pullback f L hL)

private theorem affineDeterminantValue_congr {X Z : Scheme.{u}} [IsAffine Z]
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L)
    {p q : Z ⟶ X} (e : p = q) :
    twoTermDeterminantIso (A.functor Z) (twoTermPerfect_pullback p L hL)
        (twoTermPerfect_pullback q L hL)
        (eqToIso (congrArg (fun k ↦ (derivedPullback k).obj L) e)) =
      eqToIso (congrArg (affineDeterminantValue κ A L hL Z) e) := by
  subst q
  apply Iso.ext
  exact determinantIso_refl _ _ _

private theorem affineComparison_change {X Y Z W : Scheme.{u}}
    [IsAffine Z] [IsAffine W] (f : Y ⟶ X) (g : Z ⟶ Y) (h : W ⟶ Z)
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) :
    (pullback h).mapIso (derivedDeterminantComp κ A g f L hL).symm ≪≫
        (affineDeterminantFamily κ A ((derivedPullback f).obj L)
          (twoTermPerfect_pullback f L hL)).iso g h (h ≫ g) rfl ≪≫
        derivedDeterminantComp κ A (h ≫ g) f L hL ≪≫
        eqToIso (congrArg (affineDeterminantValue κ A L hL W)
          (Category.assoc h g f)) =
      (affineDeterminantFamily κ A L hL).iso (g ≫ f) h (h ≫ g ≫ f) rfl := by
  have hd := congrArg (fun t ↦ (twoTermDeterminantIso (A.functor W)
    (twoTermPerfect_pullback h _ (twoTermPerfect_pullback g _
      (twoTermPerfect_pullback f L hL)))
    (twoTermPerfect_pullback (h ≫ g ≫ f) L hL) t).hom)
    (derived_comp_assoc κ f g h L)
  rw [determinantIso_trans (hM := twoTermPerfect_pullback h _
    (twoTermPerfect_pullback (g ≫ f) L hL)),
    determinantIso_trans (hM := twoTermPerfect_pullback (h ≫ g) _
      (twoTermPerfect_pullback f L hL)),
    determinantIso_trans (hM := twoTermPerfect_pullback ((h ≫ g) ≫ f) L hL),
    affineDeterminantValue_congr κ A L hL (Category.assoc h g f)] at hd
  apply Iso.ext
  apply (cancel_epi ((pullback h).map (derivedDeterminantComp κ A g f L hL).hom)).1
  dsimp only [affineDeterminantFamily]
  rw [affineDeterminantComparison_eq, affineDeterminantComparison_eq]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [ordinaryAffinePullback_naturality_assoc]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ (ordinaryAffinePullback κ A h ((derivedPullback g).obj
      ((derivedPullback f).obj L))
      (twoTermPerfect_pullback g _ (twoTermPerfect_pullback f L hL))).hom ≫ k) hd.symm

private noncomputable def globalDeterminantIso {X : Scheme.{u}}
    {L M : schemeDerivedCategory X} (hL : isTwoTermPerfect X L)
    (hM : isTwoTermPerfect X M) (e : L ≅ M) :
    (affineDeterminantFamily κ A L hL).glue ≅ (affineDeterminantFamily κ A M hM).glue :=
  (affineDeterminantFamily κ A L hL).mapIso (affineDeterminantFamily κ A M hM)
    (affineDeterminantFamily_invertible κ A L hL)
    (affineDeterminantFamily_invertible κ A M hM)
    (fun Y _ f ↦ twoTermDeterminantIso (A.functor Y) (twoTermPerfect_pullback f L hL)
      (twoTermPerfect_pullback f M hM) ((derivedPullback f).mapIso e))
    (fun _Y _Z _ _ f g ↦ affineDeterminantComparison_naturality κ A hL hM e f g)

private theorem globalDeterminantIso_spec {X Y : Scheme.{u}} [IsAffine Y]
    {L M : schemeDerivedCategory X} (hL : isTwoTermPerfect X L)
    (hM : isTwoTermPerfect X M) (e : L ≅ M) (f : Y ⟶ X) :
    (pullback f).map (globalDeterminantIso κ A hL hM e).hom =
      ((affineDeterminantFamily κ A L hL).comparison
        (affineDeterminantFamily_invertible κ A L hL) f).hom ≫
      (twoTermDeterminantIso (A.functor Y) (twoTermPerfect_pullback f L hL)
        (twoTermPerfect_pullback f M hM) ((derivedPullback f).mapIso e)).hom ≫
      ((affineDeterminantFamily κ A M hM).comparison
        (affineDeterminantFamily_invertible κ A M hM) f).inv := by
  dsimp only [globalDeterminantIso]
  rw [AffineModuleFamily.mapIso_hom]
  exact (affineDeterminantFamily κ A L hL).map_spec _ _ _ _
    (fun _Y _Z _ _ f g ↦ affineDeterminantComparison_naturality κ A hL hM e f g) Y f

private theorem globalDeterminantIso_square {X Y : Scheme.{u}} [IsAffine Y]
    {L M : schemeDerivedCategory X} (hL : isTwoTermPerfect X L)
    (hM : isTwoTermPerfect X M) (e : L ≅ M) (f : Y ⟶ X) :
    (pullback f).map (globalDeterminantIso κ A hL hM e).hom ≫
        ((affineDeterminantFamily κ A M hM).comparison
          (affineDeterminantFamily_invertible κ A M hM) f).hom =
      ((affineDeterminantFamily κ A L hL).comparison
        (affineDeterminantFamily_invertible κ A L hL) f).hom ≫
      (twoTermDeterminantIso (A.functor Y) (twoTermPerfect_pullback f L hL)
        (twoTermPerfect_pullback f M hM) ((derivedPullback f).mapIso e)).hom := by
  rw [globalDeterminantIso_spec]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

attribute [local irreducible] globalDeterminantIso

private noncomputable def globalDeterminantFunctor (X : Scheme.{u}) :
    TwoTermPerfectCore X ⥤ Core X.Modules where
  obj L := Core.mk ((affineDeterminantFamily κ A L.of.obj L.of.property).glue)
  map {L M} e := CoreHom.mk (globalDeterminantIso κ A L.of.property M.of.property
    ((isTwoTermPerfect X).ι.mapIso e.iso))
  map_id L := by
    apply Core.hom_ext
    apply source_affine_hom_ext
    intro U
    change (pullback U.1.ι).map (globalDeterminantIso κ A L.of.property L.of.property
      ((isTwoTermPerfect X).ι.mapIso (Iso.refl L.of))).hom = (pullback U.1.ι).map (𝟙 _)
    rw [CategoryTheory.Functor.map_id, globalDeterminantIso_spec]
    have he : (isTwoTermPerfect X).ι.mapIso (Iso.refl L.of) = Iso.refl L.of.obj := by
      apply Iso.ext
      exact (isTwoTermPerfect X).ι.map_id L.of
    rw [he, Functor.mapIso_refl, determinantIso_refl]
    let c := (affineDeterminantFamily κ A L.of.obj L.of.property).comparison
      (affineDeterminantFamily_invertible κ A L.of.obj L.of.property) U.1.ι
    exact (congrArg (fun k ↦ c.hom ≫ k) (Category.id_comp c.inv)).trans c.hom_inv_id
  map_comp {L M N} e f := by
    apply Core.hom_ext
    apply source_affine_hom_ext
    intro U
    change (pullback U.1.ι).map (globalDeterminantIso κ A L.of.property N.of.property
      ((isTwoTermPerfect X).ι.mapIso (e.iso ≪≫ f.iso))).hom =
      (pullback U.1.ι).map ((globalDeterminantIso κ A L.of.property M.of.property
        ((isTwoTermPerfect X).ι.mapIso e.iso)).hom ≫
          (globalDeterminantIso κ A M.of.property N.of.property
            ((isTwoTermPerfect X).ι.mapIso f.iso)).hom)
    rw [Functor.map_comp, globalDeterminantIso_spec, globalDeterminantIso_spec,
      globalDeterminantIso_spec]
    rw [Functor.mapIso_trans, Functor.mapIso_trans,
      determinantIso_trans (hM := twoTermPerfect_pullback U.1.ι _ M.of.property)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem globalDeterminantFunctor_value {X : Scheme.{u}}
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) :
    twoTermDeterminantValue (globalDeterminantFunctor κ A X) L hL =
      (affineDeterminantFamily κ A L hL).glue := rfl

private theorem globalDeterminantFunctor_iso {X : Scheme.{u}}
    {L M : schemeDerivedCategory X} (hL : isTwoTermPerfect X L)
    (hM : isTwoTermPerfect X M) (e : L ≅ M) :
    twoTermDeterminantIso (globalDeterminantFunctor κ A X) hL hM e =
      globalDeterminantIso κ A hL hM e := by
  apply Iso.ext
  rfl

attribute [local irreducible] globalDeterminantFunctor

private noncomputable def globalModelIso {X : Scheme.{u}}
    (P : TwoTermDeterminantModel X) :
    (affineDeterminantFamily κ A (DerivedCategory.Q.obj P.complex)
      (twoTermPerfect_model P)).glue ≅ P.line :=
  ((affineDeterminantFamily κ A (DerivedCategory.Q.obj P.complex)
    (twoTermPerfect_model P)).fromModuleIso
    (affineDeterminantFamily_invertible κ A _ (twoTermPerfect_model P)) P.line
    (fun Y _ f ↦ (tensorToPullback f).symm.app P.line ≪≫ A.local_modelIso f P) (by
      intro Y Z _ _ f g
      exact tensorToPullback_transport_comp f g _ _ _ _ _ _
        (by simpa only [Iso.trans_hom, eqToIso_refl, Iso.trans_refl, Category.assoc]
          using A.local_model_naturality f g P))).symm

private noncomputable def globalZeroIso (X : Scheme.{u}) :
    (affineDeterminantFamily κ A (twoTermDeterminantZeroObject X)
      (twoTermPerfect_zero X)).glue ≅ SheafOfModules.unit X.ringCatSheaf :=
  ((affineDeterminantFamily κ A _ (twoTermPerfect_zero X)).fromModuleIso
    (affineDeterminantFamily_invertible κ A _ (twoTermPerfect_zero X)) _
    (fun Y _ f ↦ (tensorToPullback f).symm.app _ ≪≫ A.local_zeroIso f) (by
      intro Y Z _ _ f g
      exact tensorToPullback_transport_comp f g _ _ _ _ _ _
        (by simpa only [Iso.trans_hom, eqToIso_refl, Iso.trans_refl, Category.assoc]
          using A.local_zero_naturality f g))).symm

private theorem globalDeterminant_acyclic (X : Scheme.{u}) (E : X.Modules)
    (n : ℕ) (hE : E.IsFiniteLocallyFreeOfRank n) :
    ∃ z : DerivedCategory.Q.obj (TwoTermDeterminantModel.identity E n hE).complex ≅
        twoTermDeterminantZeroObject X,
      (globalModelIso κ A (TwoTermDeterminantModel.identity E n hE)).inv ≫
        (globalDeterminantIso κ A
          (twoTermPerfect_model (TwoTermDeterminantModel.identity E n hE))
          (twoTermPerfect_zero X) z).hom ≫ (globalZeroIso κ A X).hom =
      (β_ (dual (exteriorSheaf E n)) (exteriorSheaf E n)).hom ≫
        dualEvaluation (exteriorSheaf E n) := by
  obtain ⟨z, hz⟩ := A.local_acyclic X E n hE
  refine ⟨z, ?_⟩
  apply (cancel_mono (globalZeroIso κ A X).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply source_affine_hom_ext
  intro U
  simp only [Functor.map_comp, globalModelIso, globalZeroIso, Iso.symm_inv]
  rw [AffineModuleFamily.fromModuleIso_spec, AffineModuleFamily.fromModuleIso_spec,
    globalDeterminantIso_spec]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  apply (cancel_mono (((affineDeterminantFamily κ A (twoTermDeterminantZeroObject X)
    (twoTermPerfect_zero X)).comparison
    (affineDeterminantFamily_invertible κ A _ (twoTermPerfect_zero X)) U.1.ι).hom)).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc _ _ (twoTermDeterminantIso (A.functor U) _ _
    ((derivedPullback U.1.ι).mapIso z)).hom, Category.assoc, hz U U.1.ι]
  rw [← Functor.map_comp_assoc, (tensorToPullback U.1.ι).inv.naturality_assoc]

private noncomputable def globalPullbackLocalIso {X Y Z : Scheme.{u}} [IsAffine Z]
    (f : Y ⟶ X) (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L)
    (g : Z ⟶ Y) :
    (pullback g).obj ((pullback f).obj (affineDeterminantFamily κ A L hL).glue) ≅
      (affineDeterminantFamily κ A ((derivedPullback f).obj L)
        (twoTermPerfect_pullback f L hL)).obj Z g :=
  (pullbackComp g f).app _ ≪≫
    (affineDeterminantFamily κ A L hL).comparison
      (affineDeterminantFamily_invertible κ A L hL) (g ≫ f) ≪≫
    (twoTermDeterminantIso (A.functor Z)
      (twoTermPerfect_pullback g _ (twoTermPerfect_pullback f L hL))
      (twoTermPerfect_pullback (g ≫ f) L hL) ((κ.derivedComp g f).app L)).symm

private theorem globalPullbackLocalIso_comp {X Y Z W : Scheme.{u}}
    [IsAffine Z] [IsAffine W] (f : Y ⟶ X)
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L)
    (g : Z ⟶ Y) (h : W ⟶ Z) :
    (pullbackComp h g).inv.app
        ((pullback f).obj (affineDeterminantFamily κ A L hL).glue) ≫
        (pullback h).map (globalPullbackLocalIso κ A f L hL g).hom ≫
        ((affineDeterminantFamily κ A ((derivedPullback f).obj L)
          (twoTermPerfect_pullback f L hL)).iso g h (h ≫ g) rfl).hom =
      (globalPullbackLocalIso κ A f L hL (h ≫ g)).hom := by
  suffices hi : (pullbackComp h g).symm.app _ ≪≫
      (pullback h).mapIso (globalPullbackLocalIso κ A f L hL g) ≪≫
      (affineDeterminantFamily κ A ((derivedPullback f).obj L)
        (twoTermPerfect_pullback f L hL)).iso g h (h ≫ g) rfl =
      globalPullbackLocalIso κ A f L hL (h ≫ g) by
    exact congrArg Iso.hom hi
  let F := affineDeterminantFamily κ A L hL
  let hF := affineDeterminantFamily_invertible κ A L hL
  have he := congrArg Iso.hom (affineComparison_change κ A f g h L hL)
  have hc := congrArg Iso.hom (F.comparison_compIso hF (g ≫ f) h)
  have ht := congrArg Iso.hom (F.comparison_congrIso hF (Category.assoc h g f))
  have hp := congrArg Iso.hom (pullback_comp_assoc_iso f g h F.glue)
  have hc' : (pullback h).map (F.comparison hF (g ≫ f)).hom ≫
      (F.iso (g ≫ f) h (h ≫ g ≫ f) rfl).hom =
    (pullbackComp h (g ≫ f)).hom.app F.glue ≫
      (F.comparison hF (h ≫ g ≫ f)).hom := by
    rw [← hc]
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.hom_inv_id_app_assoc]
  apply Iso.ext
  apply (cancel_mono ((derivedDeterminantComp κ A (h ≫ g) f L hL ≪≫
    eqToIso (congrArg (affineDeterminantValue κ A L hL W)
      (Category.assoc h g f))).hom)).1
  dsimp only [globalPullbackLocalIso]
  simp only [Functor.mapIso_trans, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_symm, Category.assoc, Iso.inv_hom_id_assoc] at he ht hp ⊢
  rw [he]
  change (pullbackComp h g).inv.app ((pullback f).obj F.glue) ≫
      (pullback h).map ((pullbackComp g f).hom.app F.glue) ≫
      (pullback h).map (F.comparison hF (g ≫ f)).hom ≫
      (F.iso (g ≫ f) h (h ≫ g ≫ f) rfl).hom =
    (pullbackComp (h ≫ g) f).hom.app F.glue ≫
      (F.comparison hF ((h ≫ g) ≫ f)).hom ≫
      (eqToIso (congrArg (F.obj W) (Category.assoc h g f))).hom
  rw [hc']
  simp only [← Category.assoc] at hp ⊢
  rw [hp]
  dsimp only [pullbackCompOfEq]
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc]
  rw [← ht]

private noncomputable def globalOrdinaryPullbackIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) :
    (pullback f).obj (affineDeterminantFamily κ A L hL).glue ≅
      (affineDeterminantFamily κ A ((derivedPullback f).obj L)
        (twoTermPerfect_pullback f L hL)).glue :=
  (affineDeterminantFamily κ A ((derivedPullback f).obj L)
    (twoTermPerfect_pullback f L hL)).fromModuleIso
    (affineDeterminantFamily_invertible κ A _ (twoTermPerfect_pullback f L hL)) _
    (fun _Z _ g ↦ globalPullbackLocalIso κ A f L hL g)
    (fun _Z _W _ _ g h ↦ globalPullbackLocalIso_comp κ A f L hL g h)

private theorem globalOrdinaryPullbackIso_spec {X Y Z : Scheme.{u}} [IsAffine Z]
    (f : Y ⟶ X) (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L)
    (g : Z ⟶ Y) :
    (pullback g).map (globalOrdinaryPullbackIso κ A f L hL).hom =
      (pullbackComp g f).hom.app _ ≫
        ((affineDeterminantFamily κ A L hL).comparison
          (affineDeterminantFamily_invertible κ A L hL) (g ≫ f)).hom ≫
        (twoTermDeterminantIso (A.functor Z)
          (twoTermPerfect_pullback g _ (twoTermPerfect_pullback f L hL))
          (twoTermPerfect_pullback (g ≫ f) L hL) ((κ.derivedComp g f).app L)).inv ≫
        ((affineDeterminantFamily κ A ((derivedPullback f).obj L)
          (twoTermPerfect_pullback f L hL)).comparison
          (affineDeterminantFamily_invertible κ A _ (twoTermPerfect_pullback f L hL))
          g).inv := by
  exact AffineModuleFamily.fromModuleIso_spec _ _ _ _
    (fun _Z _W _ _ g h ↦ globalPullbackLocalIso_comp κ A f L hL g h) g

private noncomputable def globalPullbackIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) :
    (tensorPullback f).obj (affineDeterminantFamily κ A L hL).glue ≅
      (affineDeterminantFamily κ A ((derivedPullback f).obj L)
        (twoTermPerfect_pullback f L hL)).glue :=
  (tensorToPullback f).app _ ≪≫ globalOrdinaryPullbackIso κ A f L hL

private theorem globalOrdinaryPullback_square {X Y Z : Scheme.{u}} [IsAffine Z]
    (f : Y ⟶ X) (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L)
    (g : Z ⟶ Y) :
    (pullback g).map (globalOrdinaryPullbackIso κ A f L hL).hom ≫
        ((affineDeterminantFamily κ A ((derivedPullback f).obj L)
          (twoTermPerfect_pullback f L hL)).comparison
          (affineDeterminantFamily_invertible κ A _ (twoTermPerfect_pullback f L hL))
          g).hom ≫
        (twoTermDeterminantIso (A.functor Z)
          (twoTermPerfect_pullback g _ (twoTermPerfect_pullback f L hL))
          (twoTermPerfect_pullback (g ≫ f) L hL) ((κ.derivedComp g f).app L)).hom =
      (pullbackComp g f).hom.app _ ≫
        ((affineDeterminantFamily κ A L hL).comparison
          (affineDeterminantFamily_invertible κ A L hL) (g ≫ f)).hom := by
  rw [globalOrdinaryPullbackIso_spec]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem globalOrdinaryPullback_naturality {X Y : Scheme.{u}}
    (f : Y ⟶ X) {L M : schemeDerivedCategory X}
    (hL : isTwoTermPerfect X L) (hM : isTwoTermPerfect X M) (e : L ≅ M) :
    (pullback f).map (globalDeterminantIso κ A hL hM e).hom ≫
        (globalOrdinaryPullbackIso κ A f M hM).hom =
      (globalOrdinaryPullbackIso κ A f L hL).hom ≫
        (globalDeterminantIso κ A (twoTermPerfect_pullback f L hL)
          (twoTermPerfect_pullback f M hM) ((derivedPullback f).mapIso e)).hom := by
  apply source_affine_hom_ext
  intro U
  have he : (derivedPullback U.1.ι).mapIso ((derivedPullback f).mapIso e) ≪≫
        (κ.derivedComp U.1.ι f).app M =
      (κ.derivedComp U.1.ι f).app L ≪≫ (derivedPullback (U.1.ι ≫ f)).mapIso e := by
    apply Iso.ext
    exact (κ.derivedComp U.1.ι f).hom.naturality e.hom
  have hd := congrArg (fun t ↦ (twoTermDeterminantIso (A.functor U)
    (twoTermPerfect_pullback U.1.ι _ (twoTermPerfect_pullback f L hL))
    (twoTermPerfect_pullback (U.1.ι ≫ f) M hM) t).hom) he
  rw [determinantIso_trans (hM := twoTermPerfect_pullback U.1.ι _
    (twoTermPerfect_pullback f M hM)),
    determinantIso_trans (hM := twoTermPerfect_pullback (U.1.ι ≫ f) L hL)] at hd
  have hi := iso_square_inv
    (twoTermDeterminantIso (A.functor U)
      (twoTermPerfect_pullback U.1.ι _ (twoTermPerfect_pullback f L hL))
      (twoTermPerfect_pullback (U.1.ι ≫ f) L hL) ((κ.derivedComp U.1.ι f).app L))
    (twoTermDeterminantIso (A.functor U)
      (twoTermPerfect_pullback U.1.ι _ (twoTermPerfect_pullback f M hM))
      (twoTermPerfect_pullback (U.1.ι ≫ f) M hM) ((κ.derivedComp U.1.ι f).app M))
    _ _ hd
  simp only [Functor.map_comp]
  rw [globalOrdinaryPullbackIso_spec κ A f M hM U.1.ι,
    globalOrdinaryPullbackIso_spec κ A f L hL U.1.ι,
    globalDeterminantIso_spec κ A (twoTermPerfect_pullback f L hL)
      (twoTermPerfect_pullback f M hM) ((derivedPullback f).mapIso e) U.1.ι]
  rw [pullbackComp_naturality_assoc,
    globalDeterminantIso_spec κ A hL hM e (U.1.ι ≫ f)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using congrArg (fun k ↦
    (pullbackComp U.1.ι f).hom.app (affineDeterminantFamily κ A L hL).glue ≫
      ((affineDeterminantFamily κ A L hL).comparison
        (affineDeterminantFamily_invertible κ A L hL) (U.1.ι ≫ f)).hom ≫ k ≫
      ((affineDeterminantFamily κ A ((derivedPullback f).obj M)
        (twoTermPerfect_pullback f M hM)).comparison
        (affineDeterminantFamily_invertible κ A _ (twoTermPerfect_pullback f M hM))
        U.1.ι).inv) hi

private theorem globalPullback_naturality {X Y : Scheme.{u}}
    (f : Y ⟶ X) {L M : schemeDerivedCategory X}
    (hL : isTwoTermPerfect X L) (hM : isTwoTermPerfect X M) (e : L ≅ M) :
    (tensorPullback f).map (globalDeterminantIso κ A hL hM e).hom ≫
        (globalPullbackIso κ A f M hM).hom =
      (globalPullbackIso κ A f L hL).hom ≫
        (globalDeterminantIso κ A (twoTermPerfect_pullback f L hL)
          (twoTermPerfect_pullback f M hM) ((derivedPullback f).mapIso e)).hom := by
  dsimp only [globalPullbackIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, (tensorToPullback f).hom.naturality,
    Category.assoc, globalOrdinaryPullback_naturality]
  simp only [Category.assoc]

private theorem globalOrdinaryPullback_id (X : Scheme.{u})
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) :
    (globalOrdinaryPullbackIso κ A (𝟙 X) L hL).hom ≫
        (globalDeterminantIso κ A (twoTermPerfect_pullback (𝟙 X) L hL) hL
          ((κ.derivedId X).app L)).hom =
      (pullbackId X).hom.app (affineDeterminantFamily κ A L hL).glue := by
  apply source_affine_hom_ext
  intro U
  have hu : (κ.derivedComp U.1.ι (𝟙 X)).app L ≪≫
        eqToIso (congrArg (fun k : U.1.toScheme ⟶ X ↦ (derivedPullback k).obj L)
          (Category.comp_id U.1.ι)) =
      (derivedPullback U.1.ι).mapIso ((κ.derivedId X).app L) := by
    apply Iso.ext
    have hh := congrArg (fun t ↦ t.hom.app L) (κ.right_unit U.1.ι)
    dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.id_obj] at hh
    have hid : (derivedPullback U.1.ι).map ((κ.derivedId X).hom.app L) ≫
        𝟙 ((derivedPullback U.1.ι).obj L) =
        (derivedPullback U.1.ι).map ((κ.derivedId X).hom.app L) := Category.comp_id _
    rw [hid] at hh
    simpa only [Iso.trans_hom, eqToIso.hom, eqToHom_app, Functor.mapIso_hom,
      Iso.app_hom] using hh
  have hp : (pullbackComp U.1.ι (𝟙 X)).app (affineDeterminantFamily κ A L hL).glue ≪≫
        eqToIso (congrArg (fun k : U.1.toScheme ⟶ X ↦
          (pullback k).obj (affineDeterminantFamily κ A L hL).glue)
          (Category.comp_id U.1.ι)) =
      (pullback U.1.ι).mapIso ((pullbackId X).app
        (affineDeterminantFamily κ A L hL).glue) := by
    apply Iso.ext
    have hc := congrArg (fun t ↦ t.app (affineDeterminantFamily κ A L hL).glue)
      (pseudofunctor_left_unitality U.1.ι)
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.id_obj] at hc
    have hid : (pullback U.1.ι).map ((pullbackId X).hom.app
        (affineDeterminantFamily κ A L hL).glue) ≫
        𝟙 ((pullback U.1.ι).obj (affineDeterminantFamily κ A L hL).glue) =
        (pullback U.1.ι).map ((pullbackId X).hom.app
          (affineDeterminantFamily κ A L hL).glue) := Category.comp_id _
    rw [hid] at hc
    apply (cancel_epi ((pullbackComp U.1.ι (𝟙 X)).inv.app _)).1
    simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, eqToIso.hom,
      Category.assoc, Iso.inv_hom_id_app_assoc, Category.comp_id, eqToHom_app]
      using hc.symm
  have hd := congrArg (fun e ↦ (twoTermDeterminantIso (A.functor U)
    (twoTermPerfect_pullback U.1.ι _ (twoTermPerfect_pullback (𝟙 X) L hL))
    (twoTermPerfect_pullback U.1.ι L hL) e).hom) hu
  rw [determinantIso_trans (hM := twoTermPerfect_pullback (U.1.ι ≫ 𝟙 X) L hL),
    affineDeterminantValue_congr κ A L hL (Category.comp_id U.1.ι)] at hd
  have hc := (affineDeterminantFamily κ A L hL).comparison_congr
    (affineDeterminantFamily_invertible κ A L hL) (Category.comp_id U.1.ι)
  have hs := globalOrdinaryPullback_square κ A (𝟙 X) L hL U.1.ι
  have hp' := congrArg Iso.hom hp
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, eqToIso.hom] at hp'
  simp only [Functor.map_comp]
  rw [globalDeterminantIso_spec]
  apply (cancel_mono ((affineDeterminantFamily κ A L hL).comparison
    (affineDeterminantFamily_invertible κ A L hL) U.1.ι).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hd]
  have hs' := congrArg (fun k ↦ k ≫
    (eqToIso (congrArg (affineDeterminantValue κ A L hL U)
      (Category.comp_id U.1.ι))).hom) hs
  have hc' := congrArg (fun k ↦
    (pullbackComp U.1.ι (𝟙 X)).hom.app (affineDeterminantFamily κ A L hL).glue ≫ k)
    hc.symm
  have hp'' := congrArg (fun k ↦ k ≫
    ((affineDeterminantFamily κ A L hL).comparison
      (affineDeterminantFamily_invertible κ A L hL) U.1.ι).hom) hp'
  calc
    _ = _ := by simpa only [Category.assoc] using hs'
    _ = _ := by simpa only [Category.assoc] using hc'
    _ = _ := by simpa only [Category.assoc, eqToIso.hom] using hp''


private theorem globalPullback_id (X : Scheme.{u})
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) :
    (globalPullbackIso κ A (𝟙 X) L hL).hom ≫
        (globalDeterminantIso κ A (twoTermPerfect_pullback (𝟙 X) L hL) hL
          ((κ.derivedId X).app L)).hom =
      (twoTermDeterminantPullbackId X).hom.app (affineDeterminantFamily κ A L hL).glue := by
  dsimp only [globalPullbackIso, Iso.trans_hom, Iso.app_hom]
  rw [Category.assoc, globalOrdinaryPullback_id]
  exact congrArg (fun t ↦ t.app _) (tensorToPullback_id X)

private theorem globalOrdinaryPullback_comp {X Y Z : Scheme.{u}}
    (g : Y ⟶ X) (h : Z ⟶ Y) (L : schemeDerivedCategory X)
    (hL : isTwoTermPerfect X L) :
    (pullbackComp h g).inv.app (affineDeterminantFamily κ A L hL).glue ≫
        (pullback h).map (globalOrdinaryPullbackIso κ A g L hL).hom ≫
        (globalOrdinaryPullbackIso κ A h ((derivedPullback g).obj L)
          (twoTermPerfect_pullback g L hL)).hom ≫
        (globalDeterminantIso κ A
          (twoTermPerfect_pullback h _ (twoTermPerfect_pullback g L hL))
          (twoTermPerfect_pullback (h ≫ g) L hL) ((κ.derivedComp h g).app L)).hom =
      (globalOrdinaryPullbackIso κ A (h ≫ g) L hL).hom := by
  apply source_affine_hom_ext
  intro U
  have ha : (derivedPullback U.1.ι).mapIso ((κ.derivedComp h g).app L) ≪≫
        (κ.derivedComp U.1.ι (h ≫ g)).app L =
      (κ.derivedComp U.1.ι h).app ((derivedPullback g).obj L) ≪≫
        (κ.derivedComp (U.1.ι ≫ h) g).app L ≪≫
          eqToIso (congrArg (fun k : U.1.toScheme ⟶ X ↦ (derivedPullback k).obj L)
            (Category.assoc U.1.ι h g)) := by
    apply Iso.ext
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.id_comp, Iso.app_hom, Functor.mapIso_hom,
      Functor.comp_obj, eqToIso.hom, eqToHom_app]
      using congrArg (fun t ↦ t.hom.app L) (κ.associativity U.1.ι h g)
  have hd := congrArg (fun t ↦ (twoTermDeterminantIso (A.functor U)
    (twoTermPerfect_pullback U.1.ι _ (twoTermPerfect_pullback h _
      (twoTermPerfect_pullback g L hL)))
    (twoTermPerfect_pullback (U.1.ι ≫ h ≫ g) L hL) t).hom) ha
  rw [determinantIso_trans (hM := twoTermPerfect_pullback U.1.ι _
    (twoTermPerfect_pullback (h ≫ g) L hL)),
    determinantIso_trans (hM := twoTermPerfect_pullback (U.1.ι ≫ h) _
      (twoTermPerfect_pullback g L hL)),
    determinantIso_trans (hM := twoTermPerfect_pullback ((U.1.ι ≫ h) ≫ g) L hL),
    affineDeterminantValue_congr κ A L hL (Category.assoc U.1.ι h g)] at hd
  let F := affineDeterminantFamily κ A L hL
  let hF := affineDeterminantFamily_invertible κ A L hL
  have hc := F.comparison_congr hF (Category.assoc U.1.ι h g)
  have hp := pullback_comp_assoc g h U.1.ι F.glue
  apply (cancel_mono
    (((affineDeterminantFamily κ A ((derivedPullback (h ≫ g)).obj L)
      (twoTermPerfect_pullback (h ≫ g) L hL)).comparison
      (affineDeterminantFamily_invertible κ A _
        (twoTermPerfect_pullback (h ≫ g) L hL)) U.1.ι).hom ≫
      (derivedDeterminantComp κ A U.1.ι (h ≫ g) L hL).hom)).1
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (globalDeterminantIso_square κ A _ _ _ _), hd]
  rw [reassoc_of% (globalOrdinaryPullback_square κ A _ _ _ _)]
  rw [pullbackComp_naturality_assoc]
  rw [reassoc_of% (globalOrdinaryPullback_square κ A _ _ _ _)]
  rw [← hc]
  rw [← Category.assoc
    ((pullback U.1.ι).map ((pullbackComp h g).inv.app F.glue))
    ((pullbackComp U.1.ι h).hom.app ((pullback g).obj F.glue)), hp]
  dsimp only [pullbackCompOfEq]
  simp only [F, Iso.trans_inv, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  simp only [pullbackCongr, eqToIso.inv, eqToIso.hom, eqToHom_refl, Category.id_comp]
  exact globalOrdinaryPullback_square κ A (h ≫ g) L hL U.1.ι |>.symm

private theorem globalPullback_comp {X Y Z : Scheme.{u}}
    (g : Y ⟶ X) (h : Z ⟶ Y) (L : schemeDerivedCategory X)
    (hL : isTwoTermPerfect X L) :
    (tensorPullbackSectionComp h g).hom.app (affineDeterminantFamily κ A L hL).glue ≫
        (tensorPullback h).map (globalPullbackIso κ A g L hL).hom ≫
        (globalPullbackIso κ A h ((derivedPullback g).obj L)
          (twoTermPerfect_pullback g L hL)).hom ≫
        (globalDeterminantIso κ A
          (twoTermPerfect_pullback h _ (twoTermPerfect_pullback g L hL))
          (twoTermPerfect_pullback (h ≫ g) L hL) ((κ.derivedComp h g).app L)).hom =
      (globalPullbackIso κ A (h ≫ g) L hL).hom := by
  dsimp only [globalPullbackIso, Iso.trans_hom, Iso.app_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [(tensorToPullback h).hom.naturality_assoc]
  have ht := congrArg (fun t ↦ t.app (affineDeterminantFamily κ A L hL).glue)
    (tensorToPullback_comp h g)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at ht
  rw [reassoc_of% ht]
  rw [globalOrdinaryPullback_comp]

end AffineDeterminants
end AlgebraicGeometry
end

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry


variable [d : ∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- A determinant system on affine schemes extends to every scheme by descent.
Source: Stacks Project, Perfect Complexes, Tags 0FJX and 0FJY; Descent, Tag 023T
(blueprint: lem-trf-two-term-determinant-affine-descent).

Proof: cover X by affine opens, refining until the chosen object has two-term finite
locally free models with constant ranks. Apply the given affine functor on each open.
For affine subopens of an overlap, the cartesian comparisons and the derived restriction
isomorphisms give transition isomorphisms. Naturality, the pullback composition law and
κ's associativity make these agree under further restriction and satisfy the cocycle
law. Equal maps of sheaves are detected on affine bases, so these are transitions on
whole overlaps, even when overlaps are not affine. Open covers are fpqc: they are flat,
and each affine open has a finite principal refinement. Use the explicit sheaf-gluing
construction in fpqc descent to obtain the determinant module. It is invertible locally,
hence globally. Full faithfulness glues the maps of the affine functors and proves the
functor laws. The same full faithfulness glues model comparisons and the normalized
zero and evaluation maps, and makes them independent of cover and refinement.
For g:Y→X, cover Y by affine V mapping into affine model opens U of X. Pulling a finite
locally free model back gives a two-term model for Lg*L by the flat-complex comparison.
The affine cartesian maps on V agree on affine refinements of overlaps, so glue to the
asserted comparison. Its naturality, identity law and composition law follow by
restriction to these affine covers and the corresponding equations in the given
system. κ's unit and associativity laws identify all iterated derived restrictions.
No quasi-compactness or separatedness of X or Y is used. On the empty scheme use the
empty gluing diagram, whose unique module is simultaneously zero and the unit. -/
theorem descend_affineTwoTermDeterminantData
    [∀ (X : Scheme.{u}) (U : X.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (κ : TwoTermDeterminantPullbackCoherence.{u, w})
    (A : AffineTwoTermDeterminantData κ) :
    Nonempty (TwoTermDeterminantFunctorData κ) := by
  refine ⟨{
    functor := globalDeterminantFunctor κ A
    invertible := fun X L hL ↦
      (affineDeterminantFamily κ A L hL).glue_invertible
        (affineDeterminantFamily_invertible κ A L hL)
    modelIso := globalModelIso κ A
    zeroIso := globalZeroIso κ A
    acyclic := ?_
    pullbackIso := globalPullbackIso κ A
    pullback_naturality := ?_
    pullback_id := ?_
    pullback_comp := ?_ }⟩
  · intro X E n hE
    simpa only [globalDeterminantFunctor_value, globalDeterminantFunctor_iso] using
      globalDeterminant_acyclic κ A X E n hE
  · intro X Y g L M hL hM e
    simpa only [globalDeterminantFunctor_value, globalDeterminantFunctor_iso] using
      globalPullback_naturality κ A g hL hM e
  · intro X L hL
    simpa only [globalDeterminantFunctor_value, globalDeterminantFunctor_iso] using
      globalPullback_id κ A X L hL
  · intro X Y Z g h L hL
    simpa only [globalDeterminantFunctor_value, globalDeterminantFunctor_iso] using
      globalPullback_comp κ A g h L hL

end AlgebraicGeometry
