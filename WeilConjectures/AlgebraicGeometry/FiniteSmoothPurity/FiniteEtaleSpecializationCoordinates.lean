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

private theorem derived_pullback_section_unit
    (A : Type (u + 1)) [CommRing A]
    {X S : Scheme.{u}} (s : S ⟶ X) (p : X ⟶ S) (h : s ≫ p = 𝟙 S) :
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).hom.app (𝟙_ _) =
      (ordinaryFinitePullback A s).map
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) p).hom ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) s).hom := by
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    s p (𝟙 S) h.symm).hom.app (𝟙_ _))).mp
  simp only [leftDerivedUpperStarCompSectionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Iso.hom_inv_id_app_assoc]
  rw [derived_pullback_unit_comp, derived_pullback_unit_id]

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

/-- Specialization for a closed etale section preserves graph-normalized unit coordinates.
This assertion concerns the Rees comparison alone and has no bundle integration factor.
Source: sk-prop-sp-orientation.proof.md, second displayed arrow; the proof of
lem-pur-finite-smooth-gamma-normalization, Steps 2 and 4--6.
(blueprint: lem-pur-finite-etale-specialization-coordinates).

Proof: the section is open and closed. Its ideal is zero on its image and the unit
ideal on the complement, so the extended Rees algebras are respectively O[t] and
O[t,t^-1]. The normal projection is the identity on the section component. In the
coordinates obtained from the graph-normalized etale sum adjunction, each fibre
mate is the canonical coefficient-unit pullback map: transpose the support exchange
identity and cancel the two adjunction triangles. The resulting comparison of the
family with the pullback of the section invariant is normalized at one. Uniqueness
of a comparison with this normalization identifies it with kappa. Restrict at zero
and invert; the pullback section compositor cancels, leaving the stated equality.
All formulas glue on the two clopen pieces, including empty pieces and zero rings. -/
theorem finiteEtaleSpecialization_coordinates
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (g : V ⟶ S) [HasCompactification g] [QuasiCompact g] [IsSeparated g] [Etale g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [FiniteRingSectionDeformation.Geometry 0 g s]
    [Etale (Scheme.Hom.normalConeProj g s)] [IsSeparated (Scheme.Hom.normalConeProj g s)]
    (hS : IsUnit (N : Γ(S, ⊤)))
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C)
    (kappa : NoetherianSectionSpecialization.family A g s ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant A g s))
    (hKappa : NoetherianSectionSpecialization.Normalized A g s hs kappa) :
    NoetherianSectionSpecialization.specialization A g s kappa ≫
        (finiteSmoothSectionCoordinates A C (Scheme.Hom.normalConeProj g s)
          (Scheme.Hom.normalConeZeroSection s)).hom =
      (finiteSmoothSectionCoordinates A C g s).hom := by
  have : Etale (Scheme.Hom.deformationSpaceProj g s) :=
    (Etale.iff_smoothOfRelativeDimension_zero _).mpr inferInstance
  let P := ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
  let I₁ := ordinaryFinitePullback A (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
  let I₀ := ordinaryFinitePullback A (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
  let J₁ := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)
  let J₀ := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) S)
  let F := finiteSmoothSectionCoordinates A C
    (Scheme.Hom.deformationSpaceProj g s) (Scheme.Hom.deformationSpaceSection s)
  let G := finiteSmoothSectionCoordinates A C g s
  let H := finiteSmoothSectionCoordinates A C (Scheme.Hom.normalConeProj g s)
    (Scheme.Hom.normalConeZeroSection s)
  let U := leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
  have hOne : NoetherianSectionSpecialization.atOne A g s hs ≫ G.hom =
      I₁.map F.hom ≫ (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).hom :=
    section_coordinates_baseChange A (Scheme.Hom.isPullback_deformationSpaceOneFibre g s)
      (Scheme.Hom.deformationSpaceSection s) s (Scheme.Hom.comp_deformationSpaceOneFibre hs) C hC
  have hZero : NoetherianSectionSpecialization.atZero A g s ≫ H.hom =
      I₀.map F.hom ≫ (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).hom :=
    section_coordinates_baseChange A (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
      (Scheme.Hom.deformationSpaceSection s) (Scheme.Hom.normalConeZeroSection s)
      Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace C hC
  let μ := F ≪≫ U.symm ≪≫ P.mapIso G.symm
  have hμ : NoetherianSectionSpecialization.Normalized A g s hs μ := by
    change I₁.map μ.hom ≫ J₁.hom.app (sectionInvariant A g s) = _
    apply (cancel_mono G.hom).mp
    have hn := J₁.hom.naturality G.hom
    change I₁.map (P.map G.hom) ≫ J₁.hom.app (𝟙_ _) =
      J₁.hom.app (sectionInvariant A g s) ≫ G.hom at hn
    rw [Category.assoc, ← hn, hOne]
    dsimp only [μ]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc]
    simp only [← Functor.comp_map, Iso.map_inv_hom_id_assoc]
    rw [show J₁.hom.app (𝟙_ _) = I₁.map U.hom ≫
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).hom from
      derived_pullback_section_unit A _ _ _]
    simp only [Iso.map_inv_hom_id_assoc]
  obtain ⟨κ, _, hu⟩ := FiniteRingSectionDeformation.existsUnique_normalized
    N hN A hA hS 0 g s hs
  have hEq : kappa = μ := (hu kappa hKappa).trans (hu μ hμ).symm
  rw [hEq]
  simp only [NoetherianSectionSpecialization.specialization, Category.assoc]
  change J₀.inv.app (sectionInvariant A g s) ≫ I₀.map μ.inv ≫
    NoetherianSectionSpecialization.atZero A g s ≫ H.hom = G.hom
  rw [hZero]
  dsimp only [μ]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Functor.map_comp,
    Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [← derived_pullback_section_unit A
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) S)]
  have hn := J₀.hom.naturality G.hom
  change I₀.map (P.map G.hom) ≫ J₀.hom.app (𝟙_ _) =
    J₀.hom.app (sectionInvariant A g s) ≫ G.hom at hn
  rw [hn, Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.Etale.FiniteSmoothPurity
