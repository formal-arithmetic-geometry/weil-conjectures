/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit

/-! # Projection, trace normalization, and the exceptional base-change mate. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v₁
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

private theorem normalized_mate
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {R : D ⥤ C} {F' : C' ⥤ D'} {R' : D' ⥤ C'}
    {J : C ⥤ C'} {H : D ⥤ D'} (adj : F ⊣ R) (adj' : F' ⊣ R')
    (b : F ⋙ H ≅ J ⋙ F') {X : C} {X' : C'} {K : D}
    (a : J.obj X ≅ X') (γ : X ⟶ R.obj K) (γ' : X' ⟶ R'.obj (H.obj K))
    (hc : F'.map a.hom ≫ F'.map γ' ≫ adj'.counit.app (H.obj K) =
      b.inv.app X ≫ H.map (F.map γ ≫ adj.counit.app K)) :
    J.map γ ≫ (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ b.inv)).app K =
      a.hom ≫ γ' := by
  apply (adj'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [mateEquiv_counit]
  have hn := b.inv.naturality γ
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← H.map_comp]
  exact hc.symm

private theorem projection_cartesian_tensor
    (C : Type v₁) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [Etale.UpperStarPreservesFlat C]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f']
    (sq : IsPullback g' f' f g)
    (P : Etale.derivedTensorRightDerivedLowerShriek C
        (HasCompactification.compactification f) ⟶
      Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar C
        (HasCompactification.compactification f))
    (P' : Etale.derivedTensorRightDerivedLowerShriek C
        (HasCompactification.compactification f') ⟶
      Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar C
        (HasCompactification.compactification f'))
    (β : Etale.rightDerivedLowerShriek C f ⋙ (Etale.upperStar C g).leftDerivedFunctor ⟶
      (Etale.upperStar C g').leftDerivedFunctor ⋙ Etale.rightDerivedLowerShriek C f')
    (W : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (W' : DerivedCategory (Sheaf X'.smallEtaleTopology C))
    (l : (Etale.upperStar C g').leftDerivedFunctor.obj W ≅ W')
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (hβ : (Etale.upperStar C g).leftDerivedFunctor.map
        ((P.app W).app K) ≫
      β.app (((Etale.derivedTensor C X).obj W).obj
        ((Etale.upperStar C f).leftDerivedFunctor.obj K)) ≫
      (Etale.rightDerivedLowerShriek C f').map
        (((Etale.leftDerivedUpperStarTensorComparison C g').app W).app
          ((Etale.upperStar C f).leftDerivedFunctor.obj K)) ≫
      (Etale.rightDerivedLowerShriek C f').map
        (((Etale.derivedTensor C X').obj
          ((Etale.upperStar C g').leftDerivedFunctor.obj W)).map
            (Etale.derivedSquareUpperStarIsoInvApp C sq.toCommSq K)) =
      ((Etale.leftDerivedUpperStarTensorComparison C g).app
        ((Etale.rightDerivedLowerShriek C f).obj W)).app K ≫
      ((Etale.derivedTensor C Y').map (β.app W)).app
        ((Etale.upperStar C g).leftDerivedFunctor.obj K) ≫
      (P'.app
        ((Etale.upperStar C g').leftDerivedFunctor.obj W)).app
          ((Etale.upperStar C g).leftDerivedFunctor.obj K)) :
    (Etale.upperStar C g).leftDerivedFunctor.map ((P.app W).app K) ≫
      β.app
        (W ⊗ (Etale.upperStar C f).leftDerivedFunctor.obj K) ≫
      (Etale.rightDerivedLowerShriek C f').map ((Etale.leftDerivedUpperStarTensorIso C g' W
        ((Etale.upperStar C f).leftDerivedFunctor.obj K) ≪≫
          (l ⊗ᵢ ((Etale.derivedSquareUpperStarIso C sq.toCommSq).symm.app K))).hom) =
    ((Etale.leftDerivedUpperStarTensorComparison C g).app
      ((Etale.rightDerivedLowerShriek C f).obj W)).app K ≫
      (β.app W ≫
        (Etale.rightDerivedLowerShriek C f').map l.hom) ▷
          (Etale.upperStar C g).leftDerivedFunctor.obj K ≫
      (P'.app W').app ((Etale.upperStar C g).leftDerivedFunctor.obj K) := by
  let L' := Etale.rightDerivedLowerShriek C f'
  let H := (Etale.upperStar C g).leftDerivedFunctor
  let J := (Etale.upperStar C g').leftDerivedFunctor
  let π := (P.app W).app K
  let π' := (P'.app W').app (H.obj K)
  let μ := ((Etale.leftDerivedUpperStarTensorComparison C g).app
    ((Etale.rightDerivedLowerShriek C f).obj W)).app K
  have h := hβ
  change H.map π ≫ β.app (W ⊗ (Etale.upperStar C f).leftDerivedFunctor.obj K) ≫
    L'.map (((Etale.leftDerivedUpperStarTensorComparison C g').app W).app
      ((Etale.upperStar C f).leftDerivedFunctor.obj K)) ≫
    L'.map (J.obj W ◁ (((Etale.derivedSquareUpperStarIso C sq.toCommSq).symm.app K)).hom) =
    μ ≫ (β.app W) ▷ H.obj K ≫
      (P'.app (J.obj W)).app (H.obj K) at h
  have hn := NatTrans.congr_app
    (P'.naturality l.hom) (H.obj K)
  change (L'.map l.hom) ▷ H.obj K ≫ π' =
    (P'.app (J.obj W)).app (H.obj K) ≫
      L'.map (l.hom ▷ (Etale.upperStar C f').leftDerivedFunctor.obj (H.obj K)) at hn
  simp only [Iso.trans_hom, tensorIso_hom, tensorHom_def', Functor.map_comp,
    Etale.leftDerivedUpperStarTensorIso_hom]
  change H.map π ≫ β.app (W ⊗ (Etale.upperStar C f).leftDerivedFunctor.obj K) ≫
    L'.map (((Etale.leftDerivedUpperStarTensorComparison C g').app W).app
      ((Etale.upperStar C f).leftDerivedFunctor.obj K)) ≫
    L'.map (J.obj W ◁ (((Etale.derivedSquareUpperStarIso C sq.toCommSq).symm.app K)).hom) ≫
    L'.map (l.hom ▷ (Etale.upperStar C f').leftDerivedFunctor.obj (H.obj K)) = _
  rw [reassoc_of% h, ← hn, ← comp_whiskerRight_assoc]

private theorem tensor_pullback_normalization
    (C : Type v₁) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [Etale.UpperStarPreservesFlat C]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {W : DerivedCategory (Sheaf Y.smallEtaleTopology C)}
    {W' : DerivedCategory (Sheaf Y'.smallEtaleTopology C)}
    (t : W ⟶ 𝟙_ _) (t' : W' ⟶ 𝟙_ _) (k : (Etale.upperStar C g).leftDerivedFunctor.obj W ⟶ W')
    (ht : k ≫ t' = (Etale.upperStar C g).leftDerivedFunctor.map t ≫
      (Etale.leftDerivedUpperStarUnitIso C g).hom)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    ((Etale.leftDerivedUpperStarTensorComparison C g).app W).app K ≫
      k ▷ (Etale.upperStar C g).leftDerivedFunctor.obj K ≫
      t' ▷ (Etale.upperStar C g).leftDerivedFunctor.obj K ≫
        (λ_ ((Etale.upperStar C g).leftDerivedFunctor.obj K)).hom =
      (Etale.upperStar C g).leftDerivedFunctor.map (t ▷ K ≫ (λ_ K).hom) := by
  let H := (Etale.upperStar C g).leftDerivedFunctor
  let μ := ((Etale.leftDerivedUpperStarTensorComparison C g).app W).app K
  rw [← comp_whiskerRight_assoc, ht]
  simp only [comp_whiskerRight, Category.assoc]
  have h := Etale.leftDerivedUpperStarTensorIso_hom_naturality_left g t K
  change H.map (t ▷ K) ≫
    ((Etale.leftDerivedUpperStarTensorComparison C g).app (𝟙_ _)).app K =
    μ ≫ (H.map t) ▷ H.obj K at h
  rw [← reassoc_of% h]
  have hu := Etale.leftDerivedUpperStarTensorComparison_leftUnitor_hom C g K
  change ((Etale.leftDerivedUpperStarTensorComparison C g).app
    (𝟙_ _)).app K ≫ (Etale.leftDerivedUpperStarUnitIso C g).hom ▷
      H.obj K ≫ (λ_ (H.obj K)).hom = H.map (λ_ K).hom at hu
  rw [hu]
  exact (H.map_comp _ _).symm

private theorem normalized_etale_counit
    (C : Type v₁) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [Etale.UpperStarPreservesFlat C]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (R : DerivedCategory (Sheaf Y.smallEtaleTopology C) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology C))
    (adj : Etale.rightDerivedLowerShriek C f ⊣ R)
    (W : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (t : (Etale.rightDerivedLowerShriek C f).obj W ⟶ 𝟙_ _)
    (P : Etale.derivedTensorRightDerivedLowerShriek C
        (HasCompactification.compactification f) ⟶
      Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar C
        (HasCompactification.compactification f))
    (γ : (Etale.upperStar C f).leftDerivedFunctor ⋙ tensorLeft W ⟶ R)
    (hn : IntegrationGammaNormalized (Etale.rightDerivedLowerShriek C f) R
      (Etale.upperStar C f).leftDerivedFunctor adj W t (P.app W) γ)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    (P.app W).app K ≫ (Etale.rightDerivedLowerShriek C f).map (γ.app K) ≫
      adj.counit.app K = t ▷ K ≫ (λ_ K).hom := by
  obtain ⟨m, hm, hp⟩ := hn K
  exact (congrArg (((P.app W).app K) ≫ ·) (eq_of_heq hm)).trans (eq_of_heq hp)

private theorem counit_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [MonoidalCategory D] [MonoidalCategory D']
    {L : C ⥤ D} {L' : C' ⥤ D'} {J : C ⥤ C'} {H : D ⥤ D'}
    (b : L ⋙ H ≅ J ⋙ L') {X : C} {X' : C'} {K S : D} {S' : D'}
    (a : J.obj X ≅ X') (π : S ⊗ K ⟶ L.obj X) [IsIso π]
    (π' : S' ⊗ H.obj K ⟶ L'.obj X') (c : L.obj X ⟶ K) (c' : L'.obj X' ⟶ H.obj K)
    (t : S ⟶ 𝟙_ D) (t' : S' ⟶ 𝟙_ D')
    (μ : H.obj (S ⊗ K) ⟶ H.obj S ⊗ H.obj K) (k : H.obj S ⟶ S')
    (hc : π ≫ c = t ▷ K ≫ (λ_ K).hom)
    (hc' : π' ≫ c' = t' ▷ H.obj K ≫ (λ_ (H.obj K)).hom)
    (hp : H.map π ≫ b.hom.app X ≫ L'.map a.hom = μ ≫ k ▷ H.obj K ≫ π')
    (ht : μ ≫ k ▷ H.obj K ≫ t' ▷ H.obj K ≫ (λ_ (H.obj K)).hom =
      H.map (t ▷ K ≫ (λ_ K).hom)) :
    L'.map a.hom ≫ c' = b.inv.app X ≫ H.map c := by
  have hx : H.map π ≫ b.hom.app X ≫ L'.map a.hom ≫ c' = H.map π ≫ H.map c := by
    rw [reassoc_of% hp, hc', ht, ← H.map_comp, hc]
  -- Supply these instances directly instead of searching for functorial preservation of epis.
  let : IsIso (H.map π) := Functor.map_isIso H π
  let : Epi (H.map π) := IsIso.epi_of_iso (H.map π)
  let : IsIso (b.hom.app X) := (b.app X).isIso_hom
  let : Epi (b.hom.app X) := IsIso.epi_of_iso (b.hom.app X)
  have hx' := (cancel_epi (H.map π)).1 hx
  apply (cancel_epi (b.hom.app _)).1
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hx'

/-- Projection exchange and scalar trace compatibility imply compatibility of normalized mates.
Source: current blueprint sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2.
Proof: use projection naturality in the coefficient comparison and tensor-pullback unit
compatibility. The two normalization equations identify the counit square after cancelling
the invertible projection and compact-support exchange. Transpose by the mate-counit identity.
The source comparison and the normalized families are invertible, so their equality makes
the exceptional mate invertible as well.
(blueprint: lem-pur-normalized-base-change-calculus). -/
theorem integrationNormalized_baseChange_calculus
    (C : Type v₁) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [Etale.UpperStarPreservesFlat C]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f']
    (sq : IsPullback g' f' f g)
    (P : Etale.derivedTensorRightDerivedLowerShriek C
        (HasCompactification.compactification f) ⟶
      Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar C
        (HasCompactification.compactification f))
    (P' : Etale.derivedTensorRightDerivedLowerShriek C
        (HasCompactification.compactification f') ⟶
      Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar C
        (HasCompactification.compactification f'))
    (R : DerivedCategory (Sheaf Y.smallEtaleTopology C) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology C))
    (R' : DerivedCategory (Sheaf Y'.smallEtaleTopology C) ⥤
      DerivedCategory (Sheaf X'.smallEtaleTopology C))
    (adj : Etale.rightDerivedLowerShriek C f ⊣ R)
    (adj' : Etale.rightDerivedLowerShriek C f' ⊣ R')
    (b : Etale.rightDerivedLowerShriek C f ⋙ (Etale.upperStar C g).leftDerivedFunctor ≅
      (Etale.upperStar C g').leftDerivedFunctor ⋙ Etale.rightDerivedLowerShriek C f')
    (W : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (W' : DerivedCategory (Sheaf X'.smallEtaleTopology C))
    (l : (Etale.upperStar C g').leftDerivedFunctor.obj W ≅ W')
    (t : (Etale.rightDerivedLowerShriek C f).obj W ⟶ 𝟙_ _)
    (t' : (Etale.rightDerivedLowerShriek C f').obj W' ⟶ 𝟙_ _)
    (γ : (Etale.upperStar C f).leftDerivedFunctor ⋙ tensorLeft W ⟶ R)
    (γ' : (Etale.upperStar C f').leftDerivedFunctor ⋙ tensorLeft W' ⟶ R')
    (hn : IntegrationGammaNormalized (Etale.rightDerivedLowerShriek C f) R
      (Etale.upperStar C f).leftDerivedFunctor adj W t (P.app W) γ)
    (hn' : IntegrationGammaNormalized (Etale.rightDerivedLowerShriek C f') R'
      (Etale.upperStar C f').leftDerivedFunctor adj' W' t' (P'.app W') γ')
    [IsIso P] (hi : ∀ K, IsIso (γ.app K)) (hi' : ∀ K, IsIso (γ'.app K))
    (ht : b.hom.app W ≫ (Etale.rightDerivedLowerShriek C f').map l.hom ≫ t' =
      (Etale.upperStar C g).leftDerivedFunctor.map t ≫
        (Etale.leftDerivedUpperStarUnitIso C g).hom)
    (hβ : ∀ K : DerivedCategory (Sheaf Y.smallEtaleTopology C),
      (Etale.upperStar C g).leftDerivedFunctor.map
        ((P.app W).app K) ≫
      b.hom.app (((Etale.derivedTensor C X).obj W).obj
        ((Etale.upperStar C f).leftDerivedFunctor.obj K)) ≫
      (Etale.rightDerivedLowerShriek C f').map
        (((Etale.leftDerivedUpperStarTensorComparison C g').app W).app
          ((Etale.upperStar C f).leftDerivedFunctor.obj K)) ≫
      (Etale.rightDerivedLowerShriek C f').map
        (((Etale.derivedTensor C X').obj
          ((Etale.upperStar C g').leftDerivedFunctor.obj W)).map
            (Etale.derivedSquareUpperStarIsoInvApp C sq.toCommSq K)) =
      ((Etale.leftDerivedUpperStarTensorComparison C g).app
        ((Etale.rightDerivedLowerShriek C f).obj W)).app K ≫
      ((Etale.derivedTensor C Y').map (b.hom.app W)).app
        ((Etale.upperStar C g).leftDerivedFunctor.obj K) ≫
      (P'.app
        ((Etale.upperStar C g').leftDerivedFunctor.obj W)).app
          ((Etale.upperStar C g).leftDerivedFunctor.obj K))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    let e := (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ b.inv)).app K
    let a := Etale.leftDerivedUpperStarTensorIso C g' W
      ((Etale.upperStar C f).leftDerivedFunctor.obj K) ≪≫
        (l ⊗ᵢ ((Etale.derivedSquareUpperStarIso C sq.toCommSq).symm.app K))
    IsIso e ∧ (Etale.upperStar C g').leftDerivedFunctor.map (γ.app K) ≫ e =
      a.hom ≫ γ'.app ((Etale.upperStar C g).leftDerivedFunctor.obj K) := by
  let L := Etale.rightDerivedLowerShriek C f
  let L' := Etale.rightDerivedLowerShriek C f'
  let H := (Etale.upperStar C g).leftDerivedFunctor
  let J := (Etale.upperStar C g').leftDerivedFunctor
  let a := Etale.leftDerivedUpperStarTensorIso C g' W
    ((Etale.upperStar C f).leftDerivedFunctor.obj K) ≪≫
      (l ⊗ᵢ ((Etale.derivedSquareUpperStarIso C sq.toCommSq).symm.app K))
  let π := (P.app W).app K
  let : IsIso (P.app W) := NatIso.isIso_app_of_isIso P W
  let : IsIso π := NatIso.isIso_app_of_isIso (P.app W) K
  let π' := (P'.app W').app (H.obj K)
  let c := L.map (γ.app K) ≫ adj.counit.app K
  let c' := L'.map (γ'.app (H.obj K)) ≫ adj'.counit.app (H.obj K)
  have hc : π ≫ c = t ▷ K ≫ (λ_ K).hom :=
    normalized_etale_counit C f R adj W t P γ hn K
  have hc' : π' ≫ c' = t' ▷ H.obj K ≫ (λ_ (H.obj K)).hom :=
    normalized_etale_counit C f' R' adj' W' t' P' γ' hn' (H.obj K)
  let μ := ((Etale.leftDerivedUpperStarTensorComparison C g).app (L.obj W)).app K
  have hp : H.map π ≫ b.hom.app (W ⊗ (Etale.upperStar C f).leftDerivedFunctor.obj K) ≫
      L'.map a.hom = μ ≫ (b.hom.app W ≫ L'.map l.hom) ▷ H.obj K ≫ π' :=
    projection_cartesian_tensor C sq P P' b.hom W W' l K (hβ K)
  have htensor : μ ≫ (b.hom.app W ≫ L'.map l.hom) ▷ H.obj K ≫
      t' ▷ H.obj K ≫ (λ_ (H.obj K)).hom = H.map (t ▷ K ≫ (λ_ K).hom) :=
    tensor_pullback_normalization C g t t' (b.hom.app W ≫ L'.map l.hom)
      (by simpa only [Category.assoc] using ht) K
  have hcc : L'.map a.hom ≫ c' =
      b.inv.app (W ⊗ (Etale.upperStar C f).leftDerivedFunctor.obj K) ≫ H.map c :=
    counit_square b a π π' c c' t t' μ (b.hom.app W ≫ L'.map l.hom) hc hc' hp htensor
  have he := normalized_mate adj adj' b a (γ.app K) (γ'.app (H.obj K)) hcc
  refine ⟨?_, he⟩
  have := hi K
  have := hi' (H.obj K)
  let : IsIso (J.map (γ.app K)) := Functor.map_isIso J (γ.app K)
  have : IsIso (J.map (γ.app K) ≫
      (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ b.inv)).app K) := by
    rw [he]
    exact IsIso.comp_isIso' a.isIso_hom (hi' (H.obj K))
  exact IsIso.of_isIso_comp_left (J.map (γ.app K)) _

end WeilConjectures.PurityFiniteSetting
