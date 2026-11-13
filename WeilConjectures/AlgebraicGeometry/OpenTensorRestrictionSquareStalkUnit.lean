/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso
import WeilConjectures.AlgebraicGeometry.OpenRestrictionStalkSquare

/-! # Open restriction of the tensor-pullback adjunction unit

## References

* [Stacks, Tags 0096 and 0098]
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem open_iso_eq {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] :
    openTensorRestrictionIso j =
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).leftAdjointUniq
        (Scheme.Modules.restrictAdjunction j) := by
  apply Iso.ext
  simp only [openTensorRestrictionIso, Scheme.Modules.restrictFunctorIsoPullback,
    Iso.trans_hom, Iso.symm_hom]
  ext M
  simp only [NatTrans.comp_app]
  rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.leftAdjointUniq_trans_app]

private theorem open_unit {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (M : Z.Modules) :
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).unit.app M ≫
      (Scheme.Modules.pushforward j).map ((openTensorRestrictionIso j).hom.app M) =
        (Scheme.Modules.restrictAdjunction j).unit.app M := by
  rw [open_iso_eq]
  exact Adjunction.unit_leftAdjointUniq_hom_app _ _ _

private theorem composition_unit {X Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (h : Y ⟶ X) (k : Z ⟶ X) (w : g ≫ h = k)
    (M : X.Modules) :
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction h)).unit.app M ≫
      (Scheme.Modules.pushforward h).map
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
          ((Scheme.Modules.tensorPullback h).obj M)) ≫
      (Scheme.Modules.pushforwardComp g h ≪≫ Scheme.Modules.pushforwardCongr w).hom.app
        ((Scheme.Modules.tensorPullback g).obj ((Scheme.Modules.tensorPullback h).obj M)) =
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M ≫
      (Scheme.Modules.pushforward k).map
        ((Scheme.Modules.tensorPullbackCompositionIso g h k w).hom.app M) := by
  have t := unit_conjugateEquiv_symm
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction h)).comp
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)))
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k))
    (Scheme.Modules.pushforwardComp g h ≪≫ Scheme.Modules.pushforwardCongr w).hom M
  simpa only [Functor.comp_obj, Adjunction.comp_unit_app, Category.assoc,
    Scheme.Modules.tensorPullbackCompositionIso, conjugateIsoEquiv_symm_apply_hom] using t

section
attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackCompositionIso Scheme.Modules.pushforward
  Scheme.Modules.pushforwardComp Scheme.Modules.pushforwardCongr
  openTensorRestrictionIso openTensorRestrictionSquareIso

set_option maxHeartbeats 600000 in
-- Elaborate the two composition mates with their specified adjunction units.
private theorem square_unit {X X' : Scheme.{u}} (k : X' ⟶ X) (U : X.Opens)
    (M : X.Modules) :
    let p := pullback.fst k U.ι
    let q := pullback.snd k U.ι
    let cP := Scheme.Modules.pushforwardComp p k ≪≫ Scheme.Modules.pushforwardCongr rfl
    let cQ := Scheme.Modules.pushforwardComp q U.ι ≪≫
      Scheme.Modules.pushforwardCongr pullback.condition.symm
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M ≫
      (Scheme.Modules.pushforward k).map
        ((Scheme.Modules.restrictAdjunction p).unit.app
          ((Scheme.Modules.tensorPullback k).obj M)) ≫
      (Scheme.Modules.pushforward p ⋙ Scheme.Modules.pushforward k).map
        ((openTensorRestrictionSquareIso k U).hom.app M) =
    (Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q)).unit.app
          ((Scheme.Modules.restrictFunctor U.ι).obj M)) ≫
      cQ.hom.app ((Scheme.Modules.tensorPullback q).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj M)) ≫
      cP.inv.app ((Scheme.Modules.tensorPullback q).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj M)) := by
  dsimp only
  let p := pullback.fst k U.ι
  let q := pullback.snd k U.ι
  let T {A B : Scheme.{u}} (a : A ⟶ B) := Scheme.Modules.tensorPullback a
  let H {A B : Scheme.{u}} (a : A ⟶ B) := Scheme.Modules.pushforward a
  let ak := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)
  let ap := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p)
  let aj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.ι)
  let aq := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q)
  let cP := Scheme.Modules.pushforwardComp p k ≪≫ Scheme.Modules.pushforwardCongr rfl
  let cQ := Scheme.Modules.pushforwardComp q U.ι ≪≫
    Scheme.Modules.pushforwardCongr pullback.condition.symm
  let θp := openTensorRestrictionIso p
  let θj := openTensorRestrictionIso U.ι
  let βp := Scheme.Modules.tensorPullbackCompositionIso p k (p ≫ k) rfl
  let βq := Scheme.Modules.tensorPullbackCompositionIso q U.ι (p ≫ k) pullback.condition.symm
  rw [← open_unit p, ← open_unit U.ι]
  change ak.unit.app M ≫ (H k).map
      (ap.unit.app ((T k).obj M) ≫ (H p).map (θp.hom.app ((T k).obj M))) ≫
      (H p ⋙ H k).map ((openTensorRestrictionSquareIso k U).hom.app M) =
    aj.unit.app M ≫ (H U.ι).map (θj.hom.app M) ≫
      (H U.ι).map (aq.unit.app ((Scheme.Modules.restrictFunctor U.ι).obj M)) ≫
      cQ.hom.app _ ≫ cP.inv.app _
  apply (cancel_mono (cP.hom.app _)).1
  simp only [Functor.comp_obj, Category.assoc, Functor.map_comp]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  simp only [← Functor.comp_map]
  change ak.unit.app M ≫ (H k).map (ap.unit.app ((T k).obj M)) ≫
      (H p ⋙ H k).map (θp.hom.app ((T k).obj M)) ≫
      (H p ⋙ H k).map ((openTensorRestrictionSquareIso k U).hom.app M) ≫ cP.hom.app _ =
    aj.unit.app M ≫ (H U.ι).map (θj.hom.app M) ≫
      (H U.ι).map (aq.unit.app ((Scheme.Modules.restrictFunctor U.ι).obj M)) ≫
      cQ.hom.app _
  have hcP := composition_unit p k (p ≫ k) rfl M
  have hcQ := composition_unit q U.ι (p ≫ k) pullback.condition.symm M
  have hn := aq.unit_naturality (θj.hom.app M)
  have hθ : θp.hom.app ((T k).obj M) ≫
      (openTensorRestrictionSquareIso k U).hom.app M =
    βp.inv.app M ≫ βq.hom.app M ≫ (T q).map (θj.hom.app M) := by
    simp [openTensorRestrictionSquareIso, θp, θj, βp, βq, p, q, T]
  rw [← Functor.map_comp_assoc, hθ]
  rw [cP.hom.naturality]
  erw [reassoc_of% hcP]
  simp only [← Functor.map_comp]
  have hb := βp.hom_inv_id_app_assoc M (βq.hom.app M ≫ (T q).map (θj.hom.app M))
  simp only [βp] at *
  rw [hb]
  have hn' : (H U.ι).map (θj.hom.app M) ≫
      (H U.ι).map (aq.unit.app ((Scheme.Modules.restrictFunctor U.ι).obj M)) =
    (H U.ι).map (aq.unit.app ((T U.ι).obj M)) ≫
      (H q ⋙ H U.ι).map ((T q).map (θj.hom.app M)) := by
    rw [← Functor.map_comp, ← hn, Functor.map_comp]
    rfl
  rw [reassoc_of% hn']
  conv_rhs =>
    rhs
    rhs
    erw [cQ.hom.naturality ((T q).map (θj.hom.app M))]
  have hQ := congrArg
    (fun v ↦ v ≫ (H (p ≫ k)).map ((T q).map (θj.hom.app M))) hcQ
  simpa only [Category.assoc, Functor.map_comp, βq, aj, aq, H, T, cQ] using hQ.symm

end

/-- The underived open tensor square preserves the adjunction unit on stalks. -/
theorem openTensorRestrictionSquare_stalk_unit
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U : X.Opens)
    (M : X.Modules) (z0 : (pullback k U.ι : Scheme.{u})) :
    let z := pullback.fst k U.ι z0
    let q := pullback.snd k U.ι
    let N := (Scheme.Modules.restrictFunctor U.ι).obj M
    let L0 := RingedSpace.moduleStalkFunctor (pullback k U.ι).toRingedSpace z0
    let F0 := forget₂ (ModuleCat.{u} ((pullback k U.ι).presheaf.stalk z0)) AddCommGrpCat.{u}
    let hp : k z = U.ι (q z0) :=
      congrArg (fun h : pullback k U.ι ⟶ X ↦ h z0) pullback.condition
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (k z)).map
        (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M)) ≫
      ((Scheme.Modules.tensorPullback k).obj M).presheaf.stalkPushforward
        AddCommGrpCat.{u} k.base z ≫
      (Scheme.Modules.restrictStalkNatIso (pullback.fst k U.ι) z0).inv.app
        ((Scheme.Modules.tensorPullback k).obj M) ≫
      F0.map (L0.map ((openTensorRestrictionSquareIso k U).hom.app M)) =
    (M.presheaf.stalkCongr (.of_eq hp)).hom ≫
      (Scheme.Modules.restrictStalkNatIso U.ι (q z0)).inv.app M ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (q z0)).map
        (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q)).unit.app N)) ≫
      ((Scheme.Modules.tensorPullback q).obj N).presheaf.stalkPushforward
        AddCommGrpCat.{u} q.base z0 := by
  dsimp only
  exact openRestriction_stalk_square k U M ((Scheme.Modules.tensorPullback k).obj M)
    ((Scheme.Modules.tensorPullback (pullback.snd k U.ι)).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj M))
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M)
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
      (pullback.snd k U.ι))).unit.app ((Scheme.Modules.restrictFunctor U.ι).obj M))
    ((openTensorRestrictionSquareIso k U).hom.app M) (square_unit k U M) z0

end AlgebraicGeometry.SingleComplexBaseChange
