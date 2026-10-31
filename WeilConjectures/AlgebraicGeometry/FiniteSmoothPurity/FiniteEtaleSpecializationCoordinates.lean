/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import all Mathlib.Logic.Small.Defs
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothOmegaTensorCoordinates
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphTensorCore
import all WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumRightAdjointCoherenceSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization

/-! # The rank-zero Rees comparison in etale section coordinates

Source: latest smooth-purity orientation proof, deformation factor.
(blueprint: lem-pur-finite-etale-specialization-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

attribute [local instance 100000] ordinaryFiniteDerivedCategoryInstance
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] CategoryTheory.catToReflQuiver
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] upperStar lowerStar etaleLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  leftDerivedUpperStarIsoMapDerivedCategory

private theorem omega_coordinates_sum
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f] [HasCompactification f] :
    etaleSumRightAdjointUnitIso A f
        (rightDerivedUpperShriek A f)
        (rightDerivedUpperShriekAdjunction _ f) = finiteSmoothOmegaCoordinates A C f := by
  have hc : C f (HasCompactification.compactification f) =
      canonicalEtaleCompactSupportComparison A f (HasCompactification.compactification f) := by
    apply Iso.ext_inv
    exact (normalizedComparison_eq A C hC f _).trans
      (normalizedComparison_eq_source A (canonicalEtaleCompactSupportNormalization A) f _).symm
  have hs : finiteSmoothSumComparison A C f = etaleSumSupportIso A f := by
    simp only [finiteSmoothSumComparison, etaleSumSupportIso, hc]
  unfold etaleSumRightAdjointUnitIso finiteSmoothOmegaCoordinates
  apply Iso.ext
  simp only [finiteSmoothAdjointCoordinates, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, NatTrans.comp_app, rightAdjointUniq_ofNatIsoLeft, hs,
    etaleSumRightAdjointIso, conjugateIsoEquiv_apply_hom, etaleSumPullbackUnitIso,
    Category.assoc]
  rw [ProEtale.FiniteEtaleNormalization.derivedAdj_eq]
  rfl

private theorem section_baseChange_exact
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (K : DerivedCategoryModule A Y) :
    (rightDerivedUpperShriekBaseChangeMap A sq).app K ≫
        (rightDerivedUpperShriek A f').map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).hom.app K) =
      (leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) g').hom.app
          ((rightDerivedUpperShriek A f).obj K) ≫
        (etaleHorizontalCounitRightExchange A sq
          (rightDerivedUpperShriekAdjunction _ f)
          (rightDerivedUpperShriekAdjunction _ f')).app K := by
  let M := ModuleCat.{u + 1} A
  let i := leftDerivedUpperStarIsoMapDerivedCategory M g'
  let j := leftDerivedUpperStarIsoMapDerivedCategory M g
  let B := rightDerivedLowerShriekBaseChangeMap A sq
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  have ht := mateTransport (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction A f') i j (inv B)
  have := (unboundedEtaleCompactSupport_baseChange A sq).1
  have hinv : inv (unboundedEtaleCompactSupportBaseChange A sq) =
      Functor.whiskerRight i.inv _ ≫ inv B ≫ Functor.whiskerLeft _ j.hom := by
    ext K
    apply (cancel_epi ((unboundedEtaleCompactSupportBaseChange A sq).app K)).1
    simp only [NatIso.isIso_inv_app, IsIso.hom_inv_id]
    simp only [unboundedEtaleCompactSupportBaseChange, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
    dsimp only [M, i, j, B]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, NatIso.isIso_inv_app,
      IsIso.hom_inv_id_assoc, Iso.inv_hom_id_app]
    rfl
  rw [← hinv] at ht
  have hh := NatTrans.congr_app ht K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hh
  apply (cancel_epi (i.inv.app
    ((rightDerivedUpperShriek A f).obj K))).1
  simp only [M, i, Iso.inv_hom_id_app_assoc]
  simpa only [rightDerivedUpperShriekBaseChangeMap, etaleHorizontalCounitRightExchange,
    etaleHorizontalSupportBaseChangeIso, asIso_inv, M, i, j, B,
    TwoSquare.natTrans] using hh.symm

private theorem omega_coordinates_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [Etale f] [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    [Etale f'] [IsSeparated f'] [QuasiCompact f'] [HasCompactification f']
    (sq : IsPullback g' f' f g)
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C) :
    dualizingComplexBaseChangeMap A sq ≫ (finiteSmoothOmegaCoordinates A C f').hom =
      (ordinaryFinitePullback A g').map (finiteSmoothOmegaCoordinates A C f).hom ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g').hom := by
  have hb := etaleSumRightAdjoint_baseChange A sq
    (rightDerivedUpperShriek A f)
    (rightDerivedUpperShriek A f')
    (rightDerivedUpperShriekAdjunction _ f) (rightDerivedUpperShriekAdjunction _ f')
  rw [omega_coordinates_sum A C hC f, omega_coordinates_sum A C hC f'] at hb
  let M := ModuleCat.{u + 1} A
  have hu : (leftDerivedUpperStarUnitIso M g).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory M g).hom.app (constantComplex A Y) ≫
        (etaleSumPullbackUnitIso A g).hom := by
    simp only [etaleSumPullbackUnitIso, Iso.trans_hom, Iso.app_hom,
      Iso.symm_hom, M, Iso.hom_inv_id_app_assoc]
  have hx := section_baseChange_exact A sq (constantComplex A Y)
  have hbeta := congrArg
    (fun q ↦ q ≫ (rightDerivedUpperShriek A f').map
      (etaleSumPullbackUnitIso A g).hom) hx
  simp only [Category.assoc, ← Functor.map_comp] at hbeta
  erw [← hu] at hbeta
  change dualizingComplexBaseChangeMap A sq = _ at hbeta
  rw [hbeta, Category.assoc, ← ProEtale.FiniteEtaleNormalization.sum_baseChange A sq, hb]
  rw [← (leftDerivedUpperStarIsoMapDerivedCategory M g').hom.naturality_assoc]
  simp only [etaleSumPullbackUnitIso, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom]
  dsimp only [M]
  simp only [Iso.hom_inv_id_app_assoc]
  rfl

private theorem derived_pullback_unit_comp
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (w : fg = f ≫ g) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g fg w).hom.app (𝟙_ _) ≫
        (ordinaryFinitePullback A f).map
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom =
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) fg).hom := by
  simpa only [ordinaryFinitePullback, ← leftDerivedUpperStarUnitIso_hom_eq_η] using
    leftDerivedUpperStarComp_hom_app_unit (ModuleCat.{u + 1} A) f g fg w

private theorem derived_pullback_unit_id
    (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app (𝟙_ _) =
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) (𝟙 S)).hom := by
  let M := ModuleCat.{u + 1} A
  let I := ordinaryFinitePullback A (𝟙 S)
  let η := (leftDerivedUpperStarUnitIso M (𝟙 S)).hom
  let : I.Faithful := Functor.Faithful.of_iso (leftDerivedUpperStarId M S).symm
  apply I.map_injective
  apply (cancel_epi
    ((leftDerivedUpperStarComp M (𝟙 S) (𝟙 S) (𝟙 S) (by simp)).hom.app (𝟙_ _))).mp
  dsimp only [I, ordinaryFinitePullback, M]
  rw [leftDerivedUpperStarComp_id_right_hom_app]
  apply (cancel_mono η).mp
  simpa only [η, M, ordinaryFinitePullback, Category.id_comp, Category.assoc] using
    (derived_pullback_unit_comp A (𝟙 S) (𝟙 S) (𝟙 S) (by simp)).symm

private theorem section_coordinates_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {b : Y' ⟶ Y} {v : X' ⟶ X}
    [Etale f] [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    [Etale f'] [IsSeparated f'] [QuasiCompact f'] [HasCompactification f']
    (sq : IsPullback v f' f b) (s : Y ⟶ X) (s' : Y' ⟶ X')
    (hs : s' ≫ v = b ≫ s)
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C) :
    NoetherianSectionSpecialization.sectionMap A f f' b v sq s s' hs ≫
        (finiteSmoothSectionCoordinates A C f' s').hom =
      (ordinaryFinitePullback A b).map (finiteSmoothSectionCoordinates A C f s).hom ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) b).hom := by
  dsimp only [NoetherianSectionSpecialization.sectionMap,
    finiteSmoothSectionCoordinates, Iso.trans_hom, Functor.mapIso_hom, sectionInvariant]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  rw [omega_coordinates_baseChange A sq C hC]
  simp only [Functor.map_comp, Category.assoc]
  apply (cancel_epi
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b s).hom.app _)).mp
  simp only [Iso.app_hom, Iso.app_inv, Iso.hom_inv_id_app_assoc, ordinaryFinitePullback]
  have h₁ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' v
    (b ≫ s) hs.symm).hom.naturality (finiteSmoothOmegaCoordinates A C f).hom
  have h₂ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b s).hom.naturality
    (finiteSmoothOmegaCoordinates A C f).hom
  simp only [Functor.comp_map] at h₁ h₂
  rw [← reassoc_of% h₁, ← reassoc_of% h₂]
  have hu₁ := derived_pullback_unit_comp A s' v (b ≫ s) hs.symm
  have hu₂ := derived_pullback_unit_comp A b s (b ≫ s) rfl
  dsimp only [ordinaryFinitePullback] at hu₁ hu₂
  rw [hu₁, hu₂]

end AlgebraicGeometry.Etale.FiniteSmoothPurity
