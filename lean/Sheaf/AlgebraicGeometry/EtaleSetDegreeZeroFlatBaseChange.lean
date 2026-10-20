/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres

/-!
# Degree-zero flat base change for étale sheaves of sets

Source: Stacks Project, Tags 0EYS and 0EZX; blueprint sec-smooth-base-change,
sk-prop-deg0 (blueprint: sbc-lem-degree-zero-flat-base-change).

The exchange arrow is the existing `Etale.setBaseChangeArrow`, constructed using
the unit, direct-image composition comparisons, and counit.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

-- The set-valued counterparts of the composition and restriction comparisons.
-- Keep the pullback construction folded when comparing their section maps.
private noncomputable def setComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : X ⟶ Z := f ≫ g) (ht : t = f ≫ g := by cat_disch) :
    Scheme.etaleSetPullback t ≅ Scheme.etaleSetPullback g ⋙ Scheme.etaleSetPullback f :=
  (conjugateIsoEquiv ((Etale.setUpperLowerAdjunction g).comp
    (Etale.setUpperLowerAdjunction f)) (Etale.setUpperLowerAdjunction t)).symm
      (Etale.lowerStarComp (Type (u + 1)) f g t ht)

private theorem setComp_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology (Type (u + 1)))
    (t : X ⟶ Z := f ≫ g) (ht : t = f ≫ g := by cat_disch) :
    (Etale.setUpperLowerAdjunction t).unit.app F ≫
        (Etale.lowerStar (Type (u + 1)) t).map ((setComp f g t ht).hom.app F) =
      ((Etale.setUpperLowerAdjunction g).comp (Etale.setUpperLowerAdjunction f)).unit.app F ≫
        (Etale.lowerStarComp (Type (u + 1)) f g t ht).hom.app
          ((Scheme.etaleSetPullback f).obj ((Scheme.etaleSetPullback g).obj F)) := by
  have hc : conjugateEquiv ((Etale.setUpperLowerAdjunction g).comp
      (Etale.setUpperLowerAdjunction f)) (Etale.setUpperLowerAdjunction t)
      (setComp f g t ht).hom = (Etale.lowerStarComp (Type (u + 1)) f g t ht).hom :=
    congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply _)
  have hh := unit_conjugateEquiv ((Etale.setUpperLowerAdjunction g).comp
    (Etale.setUpperLowerAdjunction f)) (Etale.setUpperLowerAdjunction t)
    (setComp f g t ht).hom F
  rw [hc] at hh
  exact hh.symm

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback

private noncomputable def setRestriction {X U : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    Scheme.etaleSetPullback j ≅
      Etale.localizationRestriction (Type (u + 1)) j inferInstance :=
  (Etale.setUpperLowerAdjunction j).leftAdjointUniq
    (Etale.localizationRestrictionLowerStarAdjunction (Type (u + 1)) j inferInstance)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_unit
    {T Y : Scheme.{u}} (f : T ⟶ Y) [Etale f]
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (b : Y.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj b) :
    ((Etale.setUpperLowerAdjunction f).unit.app F).hom.app (op b) ≫
        ((Scheme.etaleSetPullback f).obj F).obj.map ψ.op ≫
        ((setRestriction f).hom.app
          F).hom.app (op c) =
      F.obj.map (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance
        _root_.trivial).homEquiv c b).symm ψ).op := by
  let A := Type (u + 1)
  let ρ := (setRestriction f).hom.app F
  have hu := congrArg (fun α ↦ α.hom.app (op b))
    (Adjunction.unit_leftAdjointUniq_hom_app (Etale.setUpperLowerAdjunction f)
      (Etale.localizationRestrictionLowerStarAdjunction A f inferInstance) F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  rw [ρ.hom.naturality, ← Category.assoc]
  erw [show ((Etale.setUpperLowerAdjunction f).unit.app F).hom.app (op b) ≫
    ρ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj b)) =
    ((Etale.localizationRestrictionLowerStarAdjunction A f inferInstance).unit.app F).hom.app
      (op b) from hu]
  change (𝟙 _ ≫ F.obj.map _ ≫ 𝟙 _) ≫ F.obj.map _ = _
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem composition_unit
    {T Y R : Scheme.{u}}
    (f : T ⟶ Y) (g : Y ⟶ R) (t : T ⟶ R) (ht : t = f ≫ g)
    (F : Sheaf R.smallEtaleTopology (Type (u + 1)))
    (b : R.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj b) :
    ((Etale.setUpperLowerAdjunction t).unit.app F).hom.app (op b) ≫
        ((Scheme.etaleSetPullback t).obj F).obj.map ψ.op ≫
        ((setComp f g t ht).hom.app F).hom.app (op c) =
      ((Etale.setUpperLowerAdjunction g).unit.app F).hom.app (op b) ≫
        ((Etale.setUpperLowerAdjunction f).unit.app
          ((Scheme.etaleSetPullback g).obj F)).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) ≫
        ((Scheme.etaleSetPullback f).obj ((Scheme.etaleSetPullback g).obj F)).obj.map
          (ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g t ht).hom.app
            b).op := by
  let A := Type (u + 1)
  have h := congrArg (fun α ↦ α.hom.app (op b))
    (setComp_unit f g F t ht)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.comp_unit_app, Etale.lowerStarComp,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at h
  rw [((setComp f g t ht).hom.app F).hom.naturality, ← Category.assoc]
  erw [h]
  simp only [Functor.comp_obj, Iso.symm_inv, Etale.lowerStar_map_hom_app, Category.assoc,
    ← Functor.map_comp, ← op_comp]

attribute [local irreducible] setComp setRestriction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Set-valued version of the chart comparison: restriction and composition of inverse
images carry the chart section map to the terminal-object unit map. The comparison
preserves the units. Source: Stacks Project, Tag 0EZX, proof. -/
private theorem setChartSections_objectComparison
    {X S : Scheme.{u}} (p : X ⟶ S)
    (G : Sheaf S.smallEtaleTopology (Type (u + 1)))
    {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ p).obj V) :
    let a := Arrow.mk
      (((Etale.setUpperLowerAdjunction p).unit.app G).hom.app (op V) ≫
        ((Scheme.etaleSetPullback p).obj G).obj.map φ.op)
    let b := Arrow.mk
      (((Etale.setUpperLowerAdjunction
          (φ.left ≫ pullback.fst V.hom p)).unit.app
            ((Scheme.etaleSetPullback V.hom).obj G)).hom.app
              (op (Scheme.Etale.mk (𝟙 V.left))))
    Nonempty (∃ (e₁ : a.left ≅ b.left) (e₂ : a.right ≅ b.right),
      e₁.hom ≫ b.hom = a.hom ≫ e₂.hom) := by
  classical
  let A := Type (u + 1)
  let j := W.hom
  let r := V.hom
  let q := φ.left ≫ pullback.fst V.hom p
  let t := j ≫ p
  have ht : t = q ≫ r := by
    dsimp [t, j, q, r]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    simpa using congrArg (· ≫ p) φ.w.symm
  let w : W.left.Etale := Scheme.Etale.mk (𝟙 W.left)
  let v : V.left.Etale := Scheme.Etale.mk (𝟙 V.left)
  let eW : (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj w ≅ W :=
    MorphismProperty.Over.isoMk (Iso.refl W.left) (by simp [w, j])
  let eV : (MorphismProperty.Over.map ⊤ (inferInstance : Etale r)).obj v ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp [v, r])
  let F := (Scheme.etaleSetPullback p).obj G
  let H := (Scheme.etaleSetPullback r).obj G
  let ρW := ((setRestriction j).app F)
  let ρV := ((setRestriction r).app G)
  let κ := ((setComp j p).symm ≪≫ setComp q r t ht).app G
  let z := (MorphismProperty.Over.pullback @Etale ⊤ q).obj v
  let : IsIso v.hom := inferInstanceAs (IsIso (𝟙 V.left))
  let ez : z ≅ w :=
    MorphismProperty.Over.isoMk (asIso (pullback.snd v.hom q)) (Category.comp_id _)
  let e₁ : G.obj.obj (op V) ≅ H.obj.obj (op v) :=
    G.obj.mapIso eV.op ≪≫ ((sheafSections _ A).obj (op v)).mapIso ρV.symm
  let e₂ : F.obj.obj (op W) ≅ ((Scheme.etaleSetPullback q).obj H).obj.obj (op z) :=
    F.obj.mapIso eW.op ≪≫ ((sheafSections _ A).obj (op w)).mapIso ρW.symm ≪≫
      ((sheafSections _ A).obj (op w)).mapIso κ ≪≫
        ((Scheme.etaleSetPullback q).obj H).obj.mapIso ez.op
  let δ : v ⟶ (MorphismProperty.Over.pullback @Etale ⊤ r).obj V :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 V.left) (𝟙 V.left) (by simp [r]))
      (by simp [v])
  let σ : w ⟶ (MorphismProperty.Over.pullback @Etale ⊤ j).obj W :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 W.left) (𝟙 W.left) (by simp [j]))
      (by simp [w])
  let θ : w ⟶ (MorphismProperty.Over.pullback @Etale ⊤ q).obj v := ez.inv
  let ψ : w ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj V :=
    MorphismProperty.Over.homMk
      (pullback.lift q (𝟙 W.left) (ht.symm.trans (Category.id_comp t).symm))
      (by simp [w])
  have hδ : ((Etale.setUpperLowerAdjunction r).unit.app G).hom.app (op V) ≫
      H.obj.map δ.op = e₁.hom := by
    have h := restriction_unit r G V v δ
    have hd : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ r inferInstance
        _root_.trivial).homEquiv v V).symm δ = eV.hom := by
      ext
      simp [δ, eV, Adjunction.homEquiv_counit]
    rw [hd] at h
    exact (Iso.eq_comp_inv (((sheafSections _ A).obj (op v)).mapIso ρV)).2 h
  have hσ : ((Etale.setUpperLowerAdjunction j).unit.app F).hom.app (op W) ≫
      ((Scheme.etaleSetPullback j).obj F).obj.map σ.op =
        F.obj.map eW.hom.op ≫ ρW.inv.hom.app (op w) := by
    have h := restriction_unit j F W w σ
    have hs : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance
        _root_.trivial).homEquiv w W).symm σ = eW.hom := by
      ext
      simp [σ, eW, Adjunction.homEquiv_counit]
    rw [hs] at h
    exact (Iso.eq_comp_inv (((sheafSections _ A).obj (op w)).mapIso ρW)).2 h
  have hχj : ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      j p t rfl).hom.app V =
      σ ≫ (MorphismProperty.Over.pullback @Etale ⊤ j).map φ := by
    apply MorphismProperty.Over.Hom.ext
    change ψ.left ≫ ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      j p t rfl).hom.app V).left =
        σ.left ≫ ((MorphismProperty.Over.pullback @Etale ⊤ j).map φ).left
    simp only [MorphismProperty.Over.pullbackComp_hom_app_left,
      MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · suffices h : φ.left ≫ pullback.fst V.hom p =
            𝟙 W.left ≫ φ.left ≫ pullback.fst V.hom p by
          simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.pullback,
            MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
            Over.homMk_left, pullback.map_id, Category.id_comp, Category.assoc,
            pullbackLeftPullbackSndIso_inv_fst, limit.lift_π, PullbackCone.mk_π_app,
            limit.lift_π_assoc, cospan_left, t, ψ, q, σ]
          exact h
        exact (Category.id_comp _).symm
      · suffices h : 𝟙 W.left ≫ j = 𝟙 W.left ≫ φ.left ≫ pullback.snd V.hom p by
          simp only [Functor.const_obj_obj, Functor.id_obj, MorphismProperty.Over.pullback,
            MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
            Over.homMk_left, pullback.map_id, Category.id_comp, Category.assoc,
            pullbackLeftPullbackSndIso_inv_fst_snd, limit.lift_π_assoc, cospan_right,
            PullbackCone.mk_π_app, limit.lift_π, cospan_left, t, ψ, q, σ]
          exact h
        have hw : j = φ.left ≫ pullback.snd V.hom p := by simpa using φ.w.symm
        exact (Category.id_comp _).trans (hw.trans (Category.id_comp _).symm)
    · simp [ψ, σ, t, MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
  have hθsnd : θ.left ≫ pullback.snd v.hom q = 𝟙 W.left := by
    have h : θ.left ≫ pullback.snd v.hom q = 𝟙 W.left ≫ 𝟙 W.left := θ.w
    exact h.trans (Category.id_comp _)
  have hθfst : θ.left ≫ pullback.fst v.hom q = q := by
    have h := congrArg (θ.left ≫ ·) (pullback.condition (f := v.hom) (g := q))
    change θ.left ≫ (pullback.fst v.hom q ≫ 𝟙 V.left) =
      θ.left ≫ (pullback.snd v.hom q ≫ q) at h
    erw [Category.comp_id, ← Category.assoc, hθsnd, Category.id_comp] at h
    exact h
  have hχq : ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      q r t ht).hom.app V =
      θ ≫ (MorphismProperty.Over.pullback @Etale ⊤ q).map δ := by
    apply MorphismProperty.Over.Hom.ext
    change ψ.left ≫ ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      q r t ht).hom.app V).left =
        θ.left ≫ ((MorphismProperty.Over.pullback @Etale ⊤ q).map δ).left
    simp only [MorphismProperty.Over.pullbackComp_hom_app_left,
      MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · suffices h : q = θ.left ≫ pullback.fst v.hom q ≫ 𝟙 V.left by
          simp only [Functor.const_obj_obj, Functor.id_obj, MorphismProperty.Over.pullback,
            MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
            Over.homMk_left, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
            limit.lift_π, PullbackCone.mk_π_app, Category.comp_id, ψ, δ]
          exact h
        exact (hθfst.symm).trans
          (congrArg (θ.left ≫ ·) (Category.comp_id _).symm)
      · suffices h : 𝟙 W.left ≫ q = θ.left ≫ pullback.fst v.hom q ≫ 𝟙 V.left by
          simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.pullback,
            MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
            Over.homMk_left, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
            limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app, Category.comp_id,
            limit.lift_π, ψ, δ]
          exact h
        exact (Category.id_comp _).trans ((hθfst.symm).trans
          (congrArg (θ.left ≫ ·) (Category.comp_id _).symm))
    · simp [ψ, hθsnd, MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
  have hj := composition_unit j p t rfl G V w ψ
  rw [hχj, op_comp, Functor.map_comp] at hj
  change _ = ((Etale.setUpperLowerAdjunction p).unit.app G).hom.app (op V) ≫
    ((Etale.setUpperLowerAdjunction j).unit.app F).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ p).obj V)) ≫
    ((j)_*[A].obj ((Scheme.etaleSetPullback j).obj F)).obj.map φ.op ≫
    ((Scheme.etaleSetPullback j).obj F).obj.map σ.op at hj
  erw [← ((Etale.setUpperLowerAdjunction j).unit.app F).hom.naturality_assoc φ.op] at hj
  erw [hσ] at hj
  have hq := composition_unit q r t ht G V w ψ
  rw [hχq, op_comp, Functor.map_comp] at hq
  change _ = ((Etale.setUpperLowerAdjunction r).unit.app G).hom.app (op V) ≫
    ((Etale.setUpperLowerAdjunction q).unit.app H).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ r).obj V)) ≫
    ((q)_*[A].obj ((Scheme.etaleSetPullback q).obj H)).obj.map δ.op ≫
    ((Scheme.etaleSetPullback q).obj H).obj.map θ.op at hq
  erw [← ((Etale.setUpperLowerAdjunction q).unit.app H).hom.naturality_assoc δ.op] at hq
  erw [reassoc_of% hδ] at hq
  let Cj := ((sheafSections _ A).obj (op w)).mapIso ((setComp j p).app G)
  let Cq := ((sheafSections _ A).obj (op w)).mapIso ((setComp q r t ht).app G)
  have hj' :
      (((Etale.setUpperLowerAdjunction p).unit.app G).hom.app (op V) ≫ F.obj.map φ.op ≫
        F.obj.map eW.hom.op ≫ ρW.inv.hom.app (op w)) ≫ Cj.inv =
      ((Etale.setUpperLowerAdjunction t).unit.app G).hom.app (op V) ≫
        ((Scheme.etaleSetPullback t).obj G).obj.map ψ.op :=
    (Iso.comp_inv_eq Cj).2 hj.symm
  have h := congrArg (· ≫ Cq.hom) hj'
  erw [Category.assoc, hq] at h
  refine ⟨⟨e₁, e₂, ?_⟩⟩
  change e₁.hom ≫ ((Etale.setUpperLowerAdjunction q).unit.app H).hom.app (op v) =
    (((Etale.setUpperLowerAdjunction p).unit.app G).hom.app (op V) ≫ F.obj.map φ.op) ≫
      e₂.hom
  apply (cancel_mono (((Scheme.etaleSetPullback q).obj H).obj.map θ.op)).mp
  dsimp [e₂, κ, Cj, Cq] at h ⊢
  simp only [Iso.op_hom] at h ⊢
  have hz : ((Scheme.etaleSetPullback q).obj H).obj.map ez.hom.op ≫
      ((Scheme.etaleSetPullback q).obj H).obj.map θ.op = 𝟙 _ :=
    (((Scheme.etaleSetPullback q).obj H).obj.mapIso ez.op).hom_inv_id
  simp only [Category.assoc] at h ⊢
  erw [hz, Category.comp_id]
  exact h.symm

private noncomputable def setSectionsMap {X S : Scheme.{u}} (p : X ⟶ S)
    (G : Sheaf S.smallEtaleTopology (Type (u + 1))) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V) :
    G.obj.obj (op V) ⟶ ((Scheme.etaleSetPullback p).obj G).obj.obj (op W) :=
  ((Etale.setUpperLowerAdjunction p).unit.app G).hom.app (op V) ≫
    ((Scheme.etaleSetPullback p).obj G).obj.map φ.op

private theorem isIso_setSectionsMap {X S : Scheme.{u}} (p : X ⟶ S)
    (G : Sheaf S.smallEtaleTopology (Type (u + 1))) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V)
    [Flat (φ.left ≫ pullback.fst V.hom p)]
    [QuasiCompact (φ.left ≫ pullback.fst V.hom p)]
    [GeometricallyConnected (φ.left ≫ pullback.fst V.hom p)] :
    IsIso (setSectionsMap p G φ) := by
  obtain ⟨⟨e₁, e₂, he⟩⟩ := setChartSections_objectComparison p G φ
  have hb := etaleSet_sections_bijective_of_flat_qc_connected_geometricFibres
    (φ.left ≫ pullback.fst V.hom p)
    (fun s ↦ GeometricallyConnected.geometrically_connectedSpace _ _ _
      (IsPullback.of_hasPullback _ _)) ((Scheme.etaleSetPullback V.hom).obj G)
  have : IsIso (((Etale.setUpperLowerAdjunction
      (φ.left ≫ pullback.fst V.hom p)).unit.app
        ((Scheme.etaleSetPullback V.hom).obj G)).hom.app
          (op (Scheme.Etale.mk (𝟙 V.left)))) := (isIso_iff_bijective _).2 hb
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk e₁ e₂ he)).2 inferInstance

-- The adjoint-transpose equation for the actual exchange map, evaluated on a chart.
private theorem setSectionsMap_comp_exchange
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : ChosenCartesianSquare h e p g)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V)
    (φ' : (MorphismProperty.Over.pullback @Etale ⊤ h).obj W ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ e).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V))
    (hφ' : φ'.left ≫ pullback.fst _ e ≫ pullback.fst V.hom g =
      pullback.fst W.hom h ≫ φ.left ≫ pullback.fst V.hom p) :
    setSectionsMap p ((Etale.lowerStar (Type (u + 1)) g).obj F) φ ≫
        (Etale.setBaseChangeArrow sq F).hom.app (op W) =
      setSectionsMap e F φ' := by
  have key : ((Scheme.etaleSetPullback p).obj
      ((Etale.lowerStar (Type (u + 1)) g).obj F)).obj.map φ.op ≫
      (Etale.setBaseChangeArrow sq F).hom.app (op W) =
      (Etale.setBaseChangeArrow sq F).hom.app _ ≫
        ((Etale.lowerStar (Type (u + 1)) h).obj ((Scheme.etaleSetPullback e).obj F)).obj.map φ.op :=
    (Etale.setBaseChangeArrow sq F).hom.naturality φ.op
  simp only [setSectionsMap, Category.assoc]
  rw [key, ← Category.assoc]
  have h2 : (Etale.setUpperLowerAdjunction p).unit.app ((Etale.lowerStar (Type (u + 1)) g).obj F) ≫
      (Etale.lowerStar (Type (u + 1)) p).map (Etale.setBaseChangeArrow sq F) =
      (Etale.lowerStar (Type (u + 1)) g).map ((Etale.setUpperLowerAdjunction e).unit.app F) ≫
        (Etale.lowerStarComp (Type (u + 1)) e g (h ≫ p) sq.w).hom.app _ ≫
        (Etale.lowerStarComp (Type (u + 1)) h p).inv.app _ := by
    let K := (Scheme.etaleSetPullback e).obj F
    let d := (Etale.lowerStarComp (Type (u + 1)) e g) ≪≫
      (Etale.lowerStarComp (Type (u + 1)) h p (e ≫ g) sq.w.symm).symm
    have he := ((Etale.setUpperLowerAdjunction p).homEquiv _ _).apply_symm_apply
      ((Etale.lowerStar (Type (u + 1)) g).map
        ((Etale.setUpperLowerAdjunction e).unit.app F) ≫ d.hom.app K)
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] at he
    change (Etale.setUpperLowerAdjunction p).unit.app _ ≫
      (Etale.lowerStar (Type (u + 1)) p).map (Etale.setBaseChangeArrow sq F) = _ at he
    have hd : d = (Etale.lowerStarComp (Type (u + 1)) e g (h ≫ p) sq.w) ≪≫
        (Etale.lowerStarComp (Type (u + 1)) h p).symm := by
      have key (d₁ d₂ : Y ⟶ S) (hd : d₁ = d₂) (w₁ w₂ w₃ w₄) :
          Etale.lowerStarComp (Type (u + 1)) e g d₁ w₁ ≪≫
              (Etale.lowerStarComp (Type (u + 1)) h p d₁ w₂).symm =
            Etale.lowerStarComp (Type (u + 1)) e g d₂ w₃ ≪≫
              (Etale.lowerStarComp (Type (u + 1)) h p d₂ w₄).symm := by
        subst hd
        rfl
      exact key _ _ sq.w.symm _ _ _ _
    simpa only [hd, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc] using he
  have h3 := congr_arg (fun f ↦ f.hom.app (op V)) h2
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h3
  erw [h3]
  simp only [Category.assoc, Etale.lowerStarComp]
  rw [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app, Etale.lowerStar_map_hom_app,
    Etale.lowerStar_obj_val_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  dsimp only [Quiver.Hom.unop_op]
  ext : 1
  have hw := MorphismProperty.Over.w φ'
  simp only [MorphismProperty.Over.pullback_obj_hom] at hw hφ' ⊢
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hφ']
      simp only [Functor.id_obj, Functor.const_obj_obj, Iso.symm_hom, Iso.symm_inv,
        MorphismProperty.Comma.comp_hom, Comma.comp_left, MorphismProperty.Over.pullback_map_left,
        MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id, Category.comp_id,
        MorphismProperty.Over.pullbackComp_hom_app_left, Category.assoc]
      erw [pullbackLeftPullbackSndIso_inv_fst]
      simp only [limit.lift_π, PullbackCone.mk_π_app, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_fst]
      erw [pullback.lift_fst_assoc]
      rw [Category.assoc]
    · simp only [Category.assoc]
      simp only [Functor.id_obj, Functor.const_obj_obj, Iso.symm_hom, Iso.symm_inv,
        MorphismProperty.Comma.comp_hom, Comma.comp_left, MorphismProperty.Over.pullback_map_left,
        MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id, Category.comp_id,
        MorphismProperty.Over.pullbackComp_hom_app_left, Category.assoc]
      erw [pullbackLeftPullbackSndIso_inv_fst_snd]
      simp only [limit.lift_π_assoc, PullbackCone.mk_π_app, Category.comp_id]
      erw [pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.lift_snd_assoc, pullback.condition]
      rw [reassoc_of% hw]
  · simp only [Category.assoc]
    simp only [Functor.id_obj, Functor.const_obj_obj, Iso.symm_hom, Iso.symm_inv,
      MorphismProperty.Comma.comp_hom, Comma.comp_left, MorphismProperty.Over.pullback_map_left,
      MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id, Category.comp_id,
      MorphismProperty.Over.pullbackComp_hom_app_left, Category.assoc]
    erw [pullbackLeftPullbackSndIso_inv_snd_snd]
    simp only [pullback.map, limit.lift_π, PullbackCone.mk_π_app, Category.comp_id]
    erw [pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd]
    rw [hw]

/-- Let `φ : W ⟶ V ×_S X` be a morphism of étale `X`-schemes, so that `W ⟶ X ⟶ S` factors
through `q : W ⟶ V`, and let `c : W ×_X Y ⟶ V ×_S T` be the induced morphism. If the square
`(e, h, g, p)` is Cartesian, then `c` is the base change of `q` along `V ×_S T ⟶ V`. -/
private lemma isPullback_pullbackFst_of_hom
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : IsPullback e h g p) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V)
    (c : pullback W.hom h ⟶ pullback V.hom g)
    (hc₁ : c ≫ pullback.fst V.hom g = pullback.fst W.hom h ≫ φ.left ≫ pullback.fst V.hom p)
    (hc₂ : c ≫ pullback.snd V.hom g = pullback.snd W.hom h ≫ e) :
    IsPullback c (pullback.fst W.hom h) (pullback.fst V.hom g)
      (φ.left ≫ pullback.fst V.hom p) := by
  have hφ : φ.left ≫ pullback.snd V.hom p = W.hom := MorphismProperty.Over.w φ
  refine IsPullback.of_right ?_ (by rw [hc₁])
    (IsPullback.of_hasPullback V.hom g).flip
  rw [hc₂, Category.assoc, pullback.condition, reassoc_of% hφ]
  exact (IsPullback.of_hasPullback W.hom h).flip.paste_horiz sq

/-- Flat, locally finitely presented base change with geometrically reduced fibres
commutes with direct image for every étale sheaf of sets.
Source: Stacks Project, Tags 0EYS, 0EZX and 0EY5
(blueprint: sbc-lem-degree-zero-flat-base-change).

Proof:
1. For every étale object over X, its composite with f is flat and locally of finite
   presentation, and has geometrically reduced fibres: use lem-pc-flat-compose,
   lem-weil-pbc-finite-presentation-base-change-composition, and
   etale-proposition-etale-reduced after every field extension. Apply
   lem-sbc-flat-reduced-etale-connected-charts to cover it by charts U → V → S,
   where V → S is étale and U → V is flat, quasi-compact, with nonempty
   geometrically connected fibres.
2. Set G = g_*F. By lem-weil-pbc-sets-etale-inverse-image-restriction and
   lem-weil-pbc-sets-etale-inverse-image-composition-units, the sections theorem
   lem-weil-pbc-etale-sections-flat-qc-connected-fibres gives the canonical
   bijection A : G(V) → (f⁻¹G)(U), compatible with the unit for f.
3. Fibre-product pasting identifies U ×_X Y with U ×_V (V ×_S T).
   The base change of U → V is flat and quasi-compact by
   lem-weil-pbc-flat-morphism-base-change and lem-pc-quasi-compact-base-change,
   and has nonempty geometrically connected fibres by their definition.
4. Apply the same sections theorem after this base change, with the restriction
   and composition comparisons, to obtain B : F(V ×_S T) → (e⁻¹F)(U ×_X Y).
   Direct-image evaluation identifies the sources of A and B. The adjoint-transpose
   equation defining exchange, and the unit equations in the comparison nodes,
   give β(U) ∘ A = B, so β(U) is bijective on each good chart.
5. Sheaf separatedness gives injectivity on every object by its good-chart cover.
   For a target section, the unique local lifts agree on overlaps by that
   injectivity. The equalizer sheaf axiom glues them, proving surjectivity.
   Inverses to the bijective components are natural and give an inverse sheaf map.
6. In the smooth case sbc-lem-smooth-criterion supplies flatness and local finite
   presentation, and sbc-lem-smooth-geometrically-reduced supplies reduced fibres.
   Apply the preceding argument. No condition on g or torsion is used. -/
theorem isIso_etaleSetDegreeZeroBaseChange_of_flat
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T}
    {f : X ⟶ S} {g : T ⟶ S} (sq : ChosenCartesianSquare h e f g)
    [Flat f] [LocallyOfFinitePresentation f]
    (hf : ∀ s : S, GeometricallyReduced (f.fiberToSpecResidueField s))
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    IsIso (Etale.setBaseChangeArrow sq F) := by
  have : GeometricallyReduced f := ⟨
    (geometrically_iff_forall_fiberToSpecResidueField).2
      (fun s ↦ (hf s).geometrically_isReduced)⟩
  have sqPB : IsPullback e h g f :=
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd).flip
  refine Sheaf.isIso_of_isIso_app_of_generate_mem _ (𝟭 (Type (u + 1))) _ fun W₀ ↦ ?_
  have : Etale W₀.hom := W₀.prop
  have : GeometricallyReduced (W₀.hom ≫ f) := GeometricallyReduced.comp_of_etale _ _
  obtain ⟨ι, U, a, V, q, r, ha, hcov, hr, hq₁, -, hq₃, -, hq₄, -, hfac⟩ :=
    exists_etaleCover_factorization (W₀.hom ≫ f)
  let W (i : ι) : X.Etale := Scheme.Etale.mk (a i ≫ W₀.hom)
  let ι' (i : ι) : W i ⟶ W₀ := MorphismProperty.Over.homMk (a i)
  refine ⟨Presieve.ofArrows W ι', (Scheme.ofArrows_mem_smallEtaleTopology_iff ι').2 ?_, ?_⟩
  · refine Set.eq_univ_iff_forall.2 fun x ↦ ?_
    obtain ⟨i, y, hy⟩ := hcov x
    exact Set.mem_iUnion.2 ⟨i, y, hy⟩
  · rintro _ _ ⟨i⟩
    let Vi : S.Etale := Scheme.Etale.mk (r i)
    let φ : W i ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj Vi :=
      MorphismProperty.Over.homMk (pullback.lift (q i) (a i ≫ W₀.hom)
        (by rw [Category.assoc]; exact hfac i)) (by simp [W])
    have hq : φ.left ≫ pullback.fst Vi.hom f = q i := by simp [φ]
    have : Flat (φ.left ≫ pullback.fst Vi.hom f) := hq ▸ hq₁ i
    have : QuasiCompact (φ.left ≫ pullback.fst Vi.hom f) := hq ▸ inferInstance
    have : GeometricallyConnected (φ.left ≫ pullback.fst Vi.hom f) := hq ▸ hq₄ i
    let c : pullback (W i).hom h ⟶ pullback Vi.hom g :=
      pullback.lift (pullback.fst (W i).hom h ≫ φ.left ≫ pullback.fst Vi.hom f)
        (pullback.snd (W i).hom h ≫ e) (by
          have hφ : φ.left ≫ pullback.snd Vi.hom f = (W i).hom := MorphismProperty.Over.w φ
          simp only [Category.assoc]
          rw [pullback.condition, reassoc_of% hφ, pullback.condition_assoc, sqPB.w])
    have hc := isPullback_pullbackFst_of_hom sqPB φ c (by simp [c]) (by simp [c])
    let φ' : (MorphismProperty.Over.pullback @Etale ⊤ h).obj (W i) ⟶
        (MorphismProperty.Over.pullback @Etale ⊤ e).obj
          ((MorphismProperty.Over.pullback @Etale ⊤ g).obj Vi) :=
      MorphismProperty.Over.homMk (pullback.lift c (pullback.snd (W i).hom h) (by simp [c]))
        (by simp)
    have hφ' : φ'.left ≫ pullback.fst _ e = c := by simp [φ']
    have : Flat (φ'.left ≫ pullback.fst _ e) :=
      hφ' ▸ MorphismProperty.of_isPullback hc.flip inferInstance
    have : QuasiCompact (φ'.left ≫ pullback.fst _ e) :=
      hφ' ▸ MorphismProperty.of_isPullback hc.flip inferInstance
    have : GeometricallyConnected (φ'.left ≫ pullback.fst _ e) :=
      hφ' ▸ MorphismProperty.of_isPullback hc.flip inferInstance
    have h₁ := isIso_setSectionsMap f ((Etale.lowerStar (Type (u + 1)) g).obj F) φ
    have h₂ := isIso_setSectionsMap e F φ'
    rw [← setSectionsMap_comp_exchange sq F φ φ'
      (by rw [reassoc_of% hφ']; simp [c])] at h₂
    exact IsIso.of_isIso_comp_left (setSectionsMap f ((Etale.lowerStar (Type (u + 1)) g).obj F) φ) _

/-- The smooth special case of degree-zero base change, with arbitrary base change
and arbitrary sheaves of sets. Source: Stacks Project, Tag 0EYS; blueprint
sk-prop-deg0, Step 4 (blueprint: sbc-lem-degree-zero-flat-base-change).

Proof: sbc-lem-smooth-criterion makes f flat and locally of finite presentation;
sbc-lem-smooth-geometrically-reduced gives geometrically reduced fibres.
Apply isIso_etaleSetDegreeZeroBaseChange_of_flat, with the same square and sheaf. -/
theorem isIso_etaleSetDegreeZeroBaseChange_of_smooth
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T}
    {f : X ⟶ S} {g : T ⟶ S} (sq : ChosenCartesianSquare h e f g) [Smooth f]
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    IsIso (Etale.setBaseChangeArrow sq F) := by
  exact isIso_etaleSetDegreeZeroBaseChange_of_flat sq (fun s ↦ inferInstance) F

end AlgebraicGeometry
