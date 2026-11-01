/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationChartCoefficientZero

/-! # Local identity-counit calculation for rank-zero bundle integration

Source: blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-vector-integration-rank-zero-local).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek upperStar lowerStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  affineLinearCompactComparison VectorBundleZeroSection.π vectorIntegrationChart
  affineLinearPullbackId leftDerivedUpperStarId
  leftDerivedUpperStarComp
set_option allowUnsafeReducibility true in
attribute [local reducible] affineTraceTower affineTraceProjection affineTraceLeftTower
  affineTraceRightTower affineLinearBaseCoefficient Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory ordinaryFinitePullback

private lemma unit_of_composition
    {C D : Type*} [Category C] [Category D]
    (P : C ⥤ D) (L : C ⥤ C) (R : D ⥤ D)
    (e : L ≅ 𝟭 C) (d : R ≅ 𝟭 D) (a : L ⋙ P ≅ P ⋙ R)
    (h : ∀ K, P.map (L.map (e.hom.app K)) ≫ a.hom.app K =
      a.hom.app (L.obj K) ≫ R.map (a.hom.app K) ≫ R.map (d.hom.app (P.obj K)))
    (K : C) : P.map (e.hom.app K) = a.hom.app K ≫ d.hom.app (P.obj K) := by
  have : R.Faithful := Functor.Faithful.of_iso d.symm
  apply R.map_injective
  rw [Functor.map_comp]
  apply (cancel_epi (a.hom.app (L.obj K))).mp
  have hn := a.hom.naturality (e.hom.app K)
  simp only [Functor.comp_map] at hn
  rw [← hn]
  simpa only [Functor.id_obj, Category.assoc] using h K

private lemma plus_comparison_congr
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f g : X ⟶ Y} [HasCompactification f] [HasCompactification g] (h : f = g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map ((rightDerivedLowerShriekPlusCongr A h).hom.app K) ≫
        (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) g).hom.app K =
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).hom.app K ≫
        (unboundedEtaleLowerShriekCongr A h).hom.app (DerivedCategory.Plus.ι.obj K) := by
  subst h
  simp only [rightDerivedLowerShriekPlusCongr, CompactSupportFormalism.lowerShriekCongr,
    unboundedEtaleLowerShriekCongr, Iso.refl_hom, NatTrans.id_app]
  erw [DerivedCategory.Plus.ι.map_id, Category.id_comp, Category.comp_id]

private lemma exchange_congr
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f g : X ⟶ Y} {f' g' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [HasCompactification f] [HasCompactification g]
    [HasCompactification f'] [HasCompactification g']
    (h : f = g) (h' : f' = g')
    (sq : IsPullback v' f' f v) (sq' : IsPullback v' g' g v)
    (K : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
        ((unboundedEtaleLowerShriekCongr A h).hom.app K) ≫
      (unboundedEtaleCompactSupportBaseChange A sq').app K =
    (unboundedEtaleCompactSupportBaseChange A sq).app K ≫
      (unboundedEtaleLowerShriekCongr A h').hom.app
        ((upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory.obj K) := by
  subst h h'
  simp [unboundedEtaleLowerShriekCongr]

private lemma identity_comparison_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S]
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map ((rightDerivedLowerShriekPlusId A S).hom.app K) =
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (𝟙 S)).hom.app K ≫
        (unboundedEtaleLowerShriekId A S).hom.app (DerivedCategory.Plus.ι.obj K) := by
  apply unit_of_composition DerivedCategory.Plus.ι
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) (𝟙 S))
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 S))
    (rightDerivedLowerShriekPlusId A S) (unboundedEtaleLowerShriekId A S)
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (𝟙 S))
  intro M
  have h := unboundedEtaleCompactSupport_composition_plus A (𝟙 S) (𝟙 S) M
  rw [rightDerivedLowerShriekPlusCompIso_id_left,
    (unboundedEtaleLowerShriekCompIso_units A (𝟙 S)).1] at h
  simp only [NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc] at h
  rw [plus_comparison_congr A (Category.id_comp (𝟙 S)).symm M] at h
  apply (cancel_mono ((unboundedEtaleLowerShriekCongr A
    (Category.id_comp (𝟙 S)).symm).hom.app (DerivedCategory.Plus.ι.obj M))).mp
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Functor.id_obj, Category.assoc] using h

private lemma identity_exchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S] (f : T ⟶ S)
    (sq : IsPullback f (𝟙 T) (𝟙 S) f) (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A f).map
        ((unboundedEtaleLowerShriekId A S).hom.app K) =
      (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (unboundedEtaleLowerShriekId A T).hom.app ((ordinaryFinitePullback A f).obj K) := by
  let P := (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
  have : IsIso (unboundedEtaleCompactSupportBaseChange A sq) :=
    (unboundedEtaleCompactSupport_baseChange A sq).1
  let a := asIso (unboundedEtaleCompactSupportBaseChange A sq)
  have h (M : DerivedCategoryModule A S) :=
    congr_app (unboundedEtaleCompactSupport_baseChange_composition A sq sq
      (by simpa only [Category.id_comp] using sq)) M
  have h' := unit_of_composition P
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 S))
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 T))
    (unboundedEtaleLowerShriekId A S) (unboundedEtaleLowerShriekId A T) a
    (fun M ↦ by
      have hm := h M
      rw [(unboundedEtaleLowerShriekCompIso_units A (𝟙 S)).1,
        (unboundedEtaleLowerShriekCompIso_units A (𝟙 T)).1] at hm
      simp only [NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.leftUnitor_hom_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Functor.map_comp, Category.assoc] at hm
      rw [exchange_congr A (Category.id_comp (𝟙 S)).symm
        (Category.id_comp (𝟙 T)).symm sq
        (by simpa only [Category.id_comp] using sq) M] at hm
      apply (cancel_mono ((unboundedEtaleLowerShriekCongr A
        (Category.id_comp (𝟙 T)).symm).hom.app (P.obj M))).mp
      simpa only [P, a, asIso_hom, Functor.comp_obj, Functor.id_obj,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
        Category.assoc] using hm) K
  apply (cancel_mono
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K)).mp
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) f).hom.naturality
      ((unboundedEtaleLowerShriekId A S).hom.app K)
  dsimp only [ordinaryFinitePullback, Functor.id_obj] at hn ⊢
  rw [hn]
  rw [h']
  simp only [a, asIso_hom, unboundedEtaleCompactSupportBaseChange,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  rw [(unboundedEtaleLowerShriekId A T).hom.naturality]
  simp only [Functor.id_map, Iso.hom_inv_id_app_assoc]

private theorem exchange_paste'
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (z : X'' ⟶ X) (b : Y'' ⟶ Y) (hz : z = w' ≫ v') (hb : b = w ≫ v)
    (sq : IsPullback z f'' f b) (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A w).map ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K) ≫
        (rightDerivedLowerShriekBaseChangeMap A sq₂).app
          ((ordinaryFinitePullback A v').obj K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v b hb).inv.app _ ≫
        (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v' z hz).hom.app K) := by
  subst hz hb
  exact affineLinearExchange_paste A sq₁ sq₂ K

private lemma pullback_id_eq (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    affineLinearPullbackId A S = leftDerivedUpperStarId (ModuleCat.{u + 1} A) S := by
  simp [affineLinearPullbackId, leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory]

end AlgebraicGeometry.Etale
