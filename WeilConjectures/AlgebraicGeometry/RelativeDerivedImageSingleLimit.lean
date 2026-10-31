/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianLimitStageSingle
import WeilConjectures.AlgebraicGeometry.RelativePullbackCoefficientSystem
import WeilConjectures.AlgebraicGeometry.AbelianLimitStageInduction

/-! # Relative continuity for a single sheaf coefficient complex

Source: Stacks Tag 0GIU, reduction to Tag 0EYM.
(blueprint: lem-sf-relative-derived-image-single-limit).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The canonical derived stage comparison is invertible for a sheaf placed in
cohomological degree zero.

Proof: in negative degrees all stage objects and the limit object vanish. In a
nonnegative degree restrict both scheme systems to the cofinal directed tail.
Pull back the fixed sheaf to every stage using the canonical coefficient maps.
Relative sheaf continuity gives the colimit comparison for these coefficients.
The coefficient colimit is the fixed-stage sheaf pulled to the limit, by
inverse-image associativity and the constant connected diagram property. The
single-sheaf and exact-pullback comparisons identify both the higher-image diagram
and every limit leg with the derived-stage diagram and its canonical cocone.
Transport the ordinary colimit across these isomorphisms.
Source: Stacks Tag 0GIU, single-sheaf case, using Tag 0EYM.
(blueprint: lem-sf-relative-derived-image-single-limit). -/
theorem relativeDerivedImage_single_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DU DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DU ⟶ DB)
    [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (DU.map h)]
    [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (DB.map h)]
    [∀ i : Iᵒᵖ, QuasiCompact (η.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (η.app i)]
    (cU : Cone DU) (hcU : IsLimit cU) (cB : Cone DB) (hcB : IsLimit cB)
    (g : cU.pt ⟶ cB.pt)
    (hg : ∀ i : Iᵒᵖ, cU.π.app i ≫ η.app i = g ≫ cB.π.app i)
    (i₀ : I) (F : Sheaf (DU.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℤ) :
    IsIso (AbelianLimitStageSystem.comparison AddCommGrpCat.{u + 1}
      (relativeLimitStageSystem DU DB η cU cB g hg i₀)
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) p) := by
  let S := relativeLimitStageSystem DU DB η cU cB g hg i₀
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  by_cases hp : p < 0
  · exact AbelianLimitStageSystem.isIso_comparison_of_lt AddCommGrpCat.{u + 1} S K 0 p hp
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ p)
  let v := (Subtype.mono_coe (· ∈ Set.Ici i₀)).functor
  let : v.Final := relativeTail_final i₀
  let : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
  let : IsConnected (Set.Ici i₀) := IsFiltered.isConnected _
  let TU := v.op ⋙ DU
  let TB := v.op ⋙ DB
  let η' := Functor.whiskerLeft v.op η
  let : ∀ {i j : (Set.Ici i₀)ᵒᵖ} (h : i ⟶ j), IsAffineHom (TU.map h) := fun h ↦ by
    dsimp only [TU, Functor.comp_map]
    infer_instance
  let : ∀ {i j : (Set.Ici i₀)ᵒᵖ} (h : i ⟶ j), IsAffineHom (TB.map h) := fun h ↦ by
    dsimp only [TB, Functor.comp_map]
    infer_instance
  let : ∀ i : (Set.Ici i₀)ᵒᵖ, QuasiCompact (η'.app i) := fun i ↦ by
    dsimp only [η', Functor.whiskerLeft_app]
    infer_instance
  let : ∀ i : (Set.Ici i₀)ᵒᵖ, QuasiSeparated (η'.app i) := fun i ↦ by
    dsimp only [η', Functor.whiskerLeft_app]
    infer_instance
  let u := cU.whisker v.op
  let b := cB.whisker v.op
  have hu : IsLimit u := (Functor.Initial.isLimitWhiskerEquiv v.op cU).symm hcU
  have hb : IsLimit b := (Functor.Initial.isLimitWhiskerEquiv v.op cB).symm hcB
  let h' : ∀ i, u.π.app i ≫ η'.app i = g ≫ b.π.app i := fun i ↦ hg (v.op.obj i)
  obtain ⟨C, e, cF, hC, ⟨hcF⟩, hcontinuity⟩ := relativeDirectImageSheaf_limit
    TU TB η' u hu b hb g h' (fun i ↦ relativePullbackSheaf DU i₀ F i)
    (relativePullbackSheafMap DU i₀ F)
    (relativePullbackSheafMap_id DU i₀ F) (relativePullbackSheafMap_comp DU i₀ F)
  obtain ⟨eF, heF⟩ := relativePullbackSheaf_colimit DU cU i₀ F C e cF hcF hC
  obtain ⟨D, eD, c, t, hD, hlegs, ⟨hc⟩⟩ := hcontinuity n
  let D₀ := AbelianLimitStageSystem.diagram AddCommGrpCat.{u + 1} S K (n : ℤ)
  let c₀ := AbelianLimitStageSystem.cocone AddCommGrpCat.{u + 1} S K (n : ℤ)
  let D₂ := opOp (Set.Ici i₀) ⋙ D₀
  let c₂ := c₀.whisker (opOp (Set.Ici i₀))
  let r : D₂ ≅ D := NatIso.ofComponents
    (fun i ↦ AbelianLimitStage.singleStageIso (S.obj (op i)) F n ≪≫ (eD i).symm)
    (by
      intro i j h
      rw [hD]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id_assoc]
      change (DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).map
          ((AbelianLimitStage.transition AddCommGrpCat.{u + 1} (S.map h.op)).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
          ((AbelianLimitStage.singleStageIso (S.obj (op j)) F n).hom ≫ (eD j).inv) =
        (AbelianLimitStage.singleStageIso (S.obj (op i)) F n).hom ≫
          AbelianLimitStage.singleStageMap (S.map h.op) F n ≫ (eD j).inv
      rw [← Category.assoc, AbelianLimitStage.singleStageIso_naturality, Category.assoc])
  let Z := relativeSheafHigherImage g
    ((upperStar AddCommGrpCat.{u + 1} (cU.π.app (op i₀))).obj F) n
  let q : c.pt ≅ Z := t ≪≫ (DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).mapIso
    ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} g).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso eF))
  let z : c₂.pt ≅ Z := AbelianLimitStage.singleStageIso S.pt F n ≪≫
    (upperStarId AddCommGrpCat.{u + 1} cB.pt).app Z
  have hw (i : Set.Ici i₀) : c₂.ι.app i ≫ z.hom = r.hom.app i ≫ c.ι.app i ≫ q.hom := by
    dsimp only [r, z, q, Iso.trans_hom, Iso.symm_hom, NatIso.ofComponents_hom_app,
      Functor.mapIso_hom, Iso.app_hom]
    simp only [Category.assoc]
    rw [reassoc_of% hlegs i]
    simp only [Iso.inv_hom_id_assoc]
    change (DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).map
        ((AbelianLimitStage.transition AddCommGrpCat.{u + 1} (S.π (op i))).app K) ≫
        (AbelianLimitStage.singleStageIso S.pt F n).hom ≫ _ = _
    rw [← Category.assoc, AbelianLimitStage.singleStageIso_naturality]
    simp only [Category.assoc]
    congr 1
    dsimp only [AbelianLimitStage.singleStageMap, S, relativeLimitStageSystem,
      relativeSheafImageLeg]
    rw [upperStarComp_id_left]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
      Category.id_comp, Category.assoc]
    rw [NatTrans.naturality, Iso.inv_hom_id_app_assoc]
    simp only [Functor.id_map]
    erw [AbelianLimitStage.relativeSheafHigherImageMap_postcomp]
    simp only [Category.assoc]
    erw [heF i]
  have hc₂ : IsColimit c₂ := by
    let c' := (Cocone.precompose r.hom).obj c
    have hc' : IsColimit c' := (IsColimit.precomposeHomEquiv r c).symm hc
    apply IsColimit.ofIsoColimit hc'
    refine (Cocone.ext (z ≪≫ q.symm) ?_).symm
    intro i
    apply (cancel_mono q.hom).mp
    simpa only [c', Cocone.precompose_obj_ι, NatTrans.comp_app, Iso.trans_hom,
      Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hw i
  have hc₀ : IsColimit c₀ := hc₂.ofWhiskerEquivalence
    (opOpEquivalence (Set.Ici i₀)).symm
  exact (colimit.isColimit D₀).nonempty_isColimit_iff_isIso_desc.mp ⟨hc₀⟩

end AlgebraicGeometry.Etale
