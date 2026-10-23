/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.SixFunctors.ProEtale.CoproductSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# The pushforward along a split finite étale cover

Let `f : X ⟶ Y` be a morphism of schemes and `G` a pro-étale sheaf on `X`. For a morphism
`h : T ⟶ X` over `k : T ⟶ Y` (i.e. `h ≫ f = k`) there is a canonical map
`k^* f_* G ⟶ h^* G` (`AlgebraicGeometry.ProEtale.lowerStarProj`): the adjoint of
`f_* G ⟶ f_* h_* h^* G ≅ k_* h^* G`, i.e. "restrict a section over `V ×_Y X` to the graph of
`V ⟶ T ⟶ X`".

Suppose that `g : U ⟶ Y` is weakly étale and that the base change of `f` along `g` is a trivial
cover `∐_{j ∈ S} U ⟶ U`, `S` finite, with the sections `sⱼ : U ⟶ X` weakly étale. Then
`g^* f_* G` is the product of the `sⱼ^* G`, with the projections `lowerStarProj`
(`AlgebraicGeometry.ProEtale.isLimitLowerStarProjFanOfIsPullback`). Indeed all these pullbacks
are restrictions along the localization functors, and on sections over `V ⟶ U` the projections
are the restrictions `G(V ×_Y X) ⟶ G(V)` along the graphs of `V ⟶ U ⟶ X`, which exhibit
`V ×_Y X = V ×_U ∐_j U` as the disjoint union of copies of `V`. This is the pro-étale
counterpart of the computation of the pushforward along a split finite étale cover
(Stacks, Tag 03QP).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

/-! ### The splitting of a base change of a trivial cover -/

section Scheme

variable {X Y U V : Scheme.{u}} {f : X ⟶ Y} {g : U ⟶ Y} {S : Type u} [Finite S]
  {fst : (∐ fun _ : S ↦ U) ⟶ X}

/-- If `∐_{j ∈ S} U ⟶ U` is the base change of `f` along `g`, then for `t : V ⟶ U` the base
change `V ×_Y X` of `f` along `t ≫ g` is the disjoint union of the graphs of the sections
`V ⟶ U ⟶ ∐_j U ⟶ X`. -/
lemma Scheme.nonempty_isColimit_cofan_pullback_lift
    (hpb : IsPullback fst (Sigma.desc fun _ ↦ 𝟙 U) f g) (t : V ⟶ U) :
    Nonempty (IsColimit (Cofan.mk (pullback (t ≫ g) f) fun j : S ↦
      pullback.lift (𝟙 V) (t ≫ Sigma.ι (fun _ : S ↦ U) j ≫ fst)
        (by rw [Category.id_comp, Category.assoc, Category.assoc, hpb.w, Sigma.ι_desc_assoc,
          Category.id_comp]))) := by
  let W := pullback (t ≫ g) f
  let p : W ⟶ ∐ fun _ : S ↦ U := hpb.lift (pullback.snd _ _) (pullback.fst _ _ ≫ t)
    (by rw [← pullback.condition, Category.assoc])
  have hp₁ : p ≫ fst = pullback.snd _ _ := hpb.lift_fst _ _ _
  have hp₂ : p ≫ Sigma.desc (fun _ ↦ 𝟙 U) = pullback.fst _ _ ≫ t := hpb.lift_snd _ _ _
  -- `W = V ×_U ∐_j U`
  have hW : IsPullback (pullback.fst (t ≫ g) f) p t (Sigma.desc fun _ ↦ 𝟙 U) :=
    IsPullback.of_bot (by rw [hp₁]; exact IsPullback.of_hasPullback _ _) hp₂.symm hpb.flip
  refine FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct _)
    (Cofan.mk W _) (Discrete.natTrans (F := Discrete.functor fun _ : S ↦ V)
      (G := Discrete.functor fun _ : S ↦ U) fun _ ↦ t) p ?_ (NatTrans.Equifibered.of_discrete _)
    fun ⟨j⟩ ↦ ?_
  · ext ⟨j⟩
    refine hpb.hom_ext ?_ ?_
    · simp [hp₁]
    · simp [hp₂]
      exact (Category.id_comp t).symm
  · refine IsPullback.of_right ?_ ?_ hW
    · simpa using IsPullback.id_horiz t
    · refine hpb.hom_ext ?_ ?_
      · simp [hp₁]
      · simp [hp₂]
        exact Category.id_comp t

end Scheme

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-! ### The projections -/

section Proj

variable {X Y T : Scheme.{u}} (f : X ⟶ Y) {h : T ⟶ X} {k : T ⟶ Y} (w : h ≫ f = k)

/-- The adjoint `f_* G ⟶ k_* h^* G` of `ProEtale.lowerStarProj`: the pushforward of the unit
`G ⟶ h_* h^* G`, followed by `f_* h_* ≅ (h ≫ f)_* = k_*`. -/
noncomputable def lowerStarProjAdj (G : Sheaf (ProEt.topology X) A) :
    (f)_*[A].obj G ⟶ (k)_*[A].obj ((h)^*[A].obj G) :=
  (f)_*[A].map ((upperStarLowerStarAdjunction A h).unit.app G) ≫
    (lowerStarComp A h f).hom.app _ ≫ (lowerStarCongr A w).hom.app _

/-- The canonical map `k^* f_* G ⟶ h^* G` for `h ≫ f = k`: the adjoint of
`f_* G ⟶ f_* h_* h^* G ≅ k_* h^* G`. -/
noncomputable def lowerStarProj (G : Sheaf (ProEt.topology X) A) :
    (k)^*[A].obj ((f)_*[A].obj G) ⟶ (h)^*[A].obj G :=
  ((upperStarLowerStarAdjunction A k).homEquiv _ _).symm (lowerStarProjAdj A f w G)

/-- The projection `ProEtale.lowerStarProj` computed with the restrictions along the
localization functors, for weakly étale `h` and `k`. -/
noncomputable def localizationRestrictionLowerStarProj (hh : WeaklyEtale h) (hk : WeaklyEtale k)
    (G : Sheaf (ProEt.topology X) A) :
    (localizationRestriction A k hk).obj ((f)_*[A].obj G) ⟶
      (localizationRestriction A h hh).obj G :=
  (localizationRestriction A k hk).map
      ((f)_*[A].map ((localizationRestrictionLowerStarAdjunction A h hh).unit.app G) ≫
        (lowerStarComp A h f).hom.app _ ≫ (lowerStarCongr A w).hom.app _) ≫
    (localizationRestrictionLowerStarAdjunction A k hk).counit.app _

/-- For weakly étale `h` and `k`, the projection `ProEtale.lowerStarProj` is the projection
computed with the restrictions along the localization functors. -/
lemma lowerStarProj_comp_upperStarIsoLocalizationRestriction_hom (hh : WeaklyEtale h)
    (hk : WeaklyEtale k) (G : Sheaf (ProEt.topology X) A) :
    lowerStarProj A f w G ≫ (upperStarIsoLocalizationRestriction A h hh).hom.app G =
      (upperStarIsoLocalizationRestriction A k hk).hom.app _ ≫
        localizationRestrictionLowerStarProj A f w hh hk G := by
  let adjh := upperStarLowerStarAdjunction A h
  let adjk := upperStarLowerStarAdjunction A k
  let ladjh := localizationRestrictionLowerStarAdjunction A h hh
  let ladjk := localizationRestrictionLowerStarAdjunction A k hk
  let θh := upperStarIsoLocalizationRestriction A h hh
  let Φ := (f)_*[A].map (ladjh.unit.app G) ≫ (lowerStarComp A h f).hom.app _ ≫
    (lowerStarCongr A w).hom.app _
  have hunit : adjh.unit.app G = ladjh.unit.app G ≫ (h)_*[A].map (θh.inv.app G) := by
    rw [← Adjunction.unit_leftAdjointUniq_hom_app adjh ladjh G, Category.assoc,
      ← Functor.map_comp]
    erw [Iso.hom_inv_id_app]
    rw [CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  have hΦ : lowerStarProjAdj A f w G = Φ ≫ (k)_*[A].map (θh.inv.app G) := by
    rw [lowerStarProjAdj, hunit, Functor.map_comp, Category.assoc]
    erw [(lowerStarComp A h f).hom.naturality_assoc, (lowerStarCongr A w).hom.naturality]
    simp only [Φ, Category.assoc]
  rw [lowerStarProj, Adjunction.homEquiv_counit, hΦ, Functor.map_comp, Category.assoc,
    Category.assoc, Adjunction.counit_naturality_assoc]
  erw [Iso.inv_hom_id_app]
  rw [Category.comp_id, ← Adjunction.leftAdjointUniq_hom_app_counit adjk ladjk,
    ← Category.assoc, (adjk.leftAdjointUniq ladjk).hom.naturality, Category.assoc]
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The restriction maps of `j_h^* G` are those of `G` along the localization functor. -/
lemma localizationRestriction_obj_obj_map (hh : WeaklyEtale h) (G : Sheaf (ProEt.topology X) A)
    {V V' : T.ProEtᵒᵖ} (φ : V ⟶ V') :
    ((localizationRestriction A h hh).obj G).obj.map φ =
      G.obj.map ((MorphismProperty.Over.map ⊤ hh).map φ.unop).op :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The unit of `j_h^* ⊣ h_*` restricts sections along the counit of the site adjunction. -/
lemma localizationRestrictionLowerStarAdjunction_unit_app_hom_app' (hh : WeaklyEtale h)
    (G : Sheaf (ProEt.topology X) A) (W : X.ProEt) :
    ((localizationRestrictionLowerStarAdjunction A h hh).unit.app G).hom.app (op W) =
      G.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ h hh trivial).counit.app
        W).op := by
  simp [localizationRestrictionLowerStarAdjunction, Adjunction.sheafPushforwardContinuous,
    Adjunction.whiskerLeft]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The counit of `j_h^* ⊣ h_*` restricts sections along the graph `V ⟶ V ×_X T`. -/
lemma localizationRestrictionLowerStarAdjunction_counit_app_hom_app' (hh : WeaklyEtale h)
    (N : Sheaf (ProEt.topology T) A) (V : T.ProEt) :
    ((localizationRestrictionLowerStarAdjunction A h hh).counit.app N).hom.app (op V) =
      N.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ h hh trivial).unit.app
        V).op := by
  simp [localizationRestrictionLowerStarAdjunction, Adjunction.sheafPushforwardContinuous]

/-- The morphism of `X_proét` from `V ⟶ T ⟶ X` to `(V ×_Y X ⟶ X)` given by the graph of
`V ⟶ T ⟶ X`, for `V` in `T_proét`. -/
noncomputable def lowerStarProjGraph (hh : WeaklyEtale h) (hk : WeaklyEtale k) (V : T.ProEt) :
    (MorphismProperty.Over.map ⊤ hh).obj V ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
        ((MorphismProperty.Over.map ⊤ hk).obj V) :=
  MorphismProperty.Over.homMk (pullback.lift (𝟙 V.left) (V.hom ≫ h)
    (by rw [Category.assoc, w]; exact Category.id_comp _))
    (by simp) trivial

/-- On sections over `V ⟶ T`, the projection `ProEtale.localizationRestrictionLowerStarProj` is
the restriction `G(V ×_Y X) ⟶ G(V)` along the graph of `V ⟶ T ⟶ X`. -/
lemma localizationRestrictionLowerStarProj_hom_app (hh : WeaklyEtale h) (hk : WeaklyEtale k)
    (G : Sheaf (ProEt.topology X) A) (V : T.ProEt) :
    (localizationRestrictionLowerStarProj A f w hh hk G).hom.app (op V) =
      G.obj.map (lowerStarProjGraph f w hh hk V).op := by
  simp only [localizationRestrictionLowerStarProj, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, localizationRestriction_map_hom_app, ProEtale.lowerStar_map_hom_app,
    localizationRestrictionLowerStarAdjunction_unit_app_hom_app',
    lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    localizationRestrictionLowerStarAdjunction_counit_app_hom_app',
    localizationRestriction_obj_obj_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  ext
  apply pullback.hom_ext
  · simp [lowerStarProjGraph, MorphismProperty.Over.pullbackCongr,
      MorphismProperty.Over.pullbackComp]
    erw [Category.id_comp, pullbackLeftPullbackSndIso_inv_fst]
    simp
    exact pullback.lift_fst (f := ((MorphismProperty.Over.map ⊤ hk).obj V).hom) (g := k) _ _ _
  · simp [lowerStarProjGraph, MorphismProperty.Over.pullbackCongr,
      MorphismProperty.Over.pullbackComp]
    erw [Category.id_comp, pullbackLeftPullbackSndIso_inv_fst_snd]
    simp
    exact congrArg (· ≫ h)
      (pullback.lift_snd (f := ((MorphismProperty.Over.map ⊤ hk).obj V).hom) (g := k) _ _ _)

end Proj

/-! ### Split covers -/

section Split

variable {X Y U : Scheme.{u}} {f : X ⟶ Y} {g : U ⟶ Y} {S : Type u} [Finite S]
  {fst : (∐ fun _ : S ↦ U) ⟶ X}

omit [Finite S] in
/-- The sections `U ⟶ ∐_j U ⟶ X` of a trivial cover lie over `g`. -/
lemma sigmaι_comp_fst_comp_eq (hpb : IsPullback fst (Sigma.desc fun _ ↦ 𝟙 U) f g) (j : S) :
    (Sigma.ι (fun _ : S ↦ U) j ≫ fst) ≫ f = g := by
  rw [Category.assoc, hpb.w, Sigma.ι_desc_assoc, Category.id_comp]

/-- **The pushforward along a split finite étale cover.** If `g : U ⟶ Y` is weakly étale and the
base change of `f` along `g` is the trivial cover `∐_{j ∈ S} U ⟶ U` with weakly étale sections
`sⱼ : U ⟶ X`, then `g^* f_* G` is the product of the `sⱼ^* G`, with the projections
`ProEtale.lowerStarProj`. -/
noncomputable def isLimitLowerStarProjFanOfIsPullback
    (hpb : IsPullback fst (Sigma.desc fun _ ↦ 𝟙 U) f g) (hg : WeaklyEtale g)
    (hs : ∀ j, WeaklyEtale (Sigma.ι (fun _ : S ↦ U) j ≫ fst)) (G : Sheaf (ProEt.topology X) A) :
    IsLimit (Fan.mk ((g)^*[A].obj ((f)_*[A].obj G)) fun j ↦
      lowerStarProj A f (sigmaι_comp_fst_comp_eq hpb j) G) := by
  have hloc : IsLimit (Fan.mk ((localizationRestriction A g hg).obj ((f)_*[A].obj G)) fun j ↦
      localizationRestrictionLowerStarProj A f (sigmaι_comp_fst_comp_eq hpb j) (hs j) hg G) := by
    refine isLimitOfReflects (sheafToPresheaf _ _) (evaluationJointlyReflectsLimits _ ?_)
    intro V
    let E := sheafToPresheaf (ProEt.topology U) A ⋙ (CategoryTheory.evaluation U.ProEtᵒᵖ A).obj V
    have hc := (Scheme.nonempty_isColimit_cofan_pullback_lift hpb V.unop.hom).some
    have hsec : IsLimit (Fan.mk (E.obj ((localizationRestriction A g hg).obj ((f)_*[A].obj G)))
        fun j ↦ E.map (localizationRestrictionLowerStarProj A f (sigmaι_comp_fst_comp_eq hpb j)
          (hs j) hg G)) := by
      refine Fan.IsLimit.ofIsos
        (ProEtale.isLimitSectionsFanOfIsColimitCofan G
          (fun j ↦ lowerStarProjGraph f (sigmaι_comp_fst_comp_eq hpb j) (hs j) hg V.unop) hc)
        (fun _ ↦ Iso.refl _) (Iso.refl _) fun j ↦ ?_
      dsimp [E]
      rw [localizationRestrictionLowerStarProj_hom_app]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    exact IsLimit.ofIsoLimit ((isLimitMapConeFanMkEquiv E _ _).symm hsec)
      (Functor.mapConeMapCone _).symm
  refine Fan.IsLimit.ofIsos hloc
    (fun j ↦ (upperStarIsoLocalizationRestriction A _ (hs j)).app G)
    ((upperStarIsoLocalizationRestriction A g hg).app _) fun j ↦ ?_
  exact (lowerStarProj_comp_upperStarIsoLocalizationRestriction_hom A f _ (hs j) hg G).symm

end Split

end ProEtale

end AlgebraicGeometry
