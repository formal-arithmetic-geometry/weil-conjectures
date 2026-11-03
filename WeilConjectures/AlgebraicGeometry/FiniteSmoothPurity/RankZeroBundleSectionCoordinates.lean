/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingBundleSectionOrientationData
import all Mathlib.Logic.Small.Defs
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteEtaleSpecializationCoordinates
import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumRightAdjointCoherenceSupplement
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteUnitCoordinateIdentifications

/-! # Rank-zero bundle section comparison in etale unit coordinates

Source: latest smooth-purity orientation proof, normal-bundle factor.
(blueprint: lem-pur-rank-zero-bundle-section-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

attribute [local instance 100000] ordinaryFiniteDerivedCategoryInstance
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] CategoryTheory.catToReflQuiver Scheme.Modules
  ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
  constantComplex sectionInvariant dualizingComplex bundleSectionOmega bundleSectionObject
  affineLinearBaseCoefficient line
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
attribute [local instance 20002] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] upperStar lowerStar etaleLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  leftDerivedUpperStarIsoMapDerivedCategory

end AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem identity_omega_coordinates
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S]
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C) :
    (finiteSmoothOmegaCoordinates A C (𝟙 S)).hom =
      ((conjugateIsoEquiv
        (rightDerivedUpperShriekAdjunction A (𝟙 S))
        (Adjunction.id)) (unboundedEtaleLowerShriekId A S).symm).hom.app (𝟙_ _) := by
  rw [← omega_coordinates_sum A C hC (𝟙 S)]
  have h := etaleSumRightAdjoint_id A S
    (rightDerivedUpperShriek A (𝟙 S))
    (rightDerivedUpperShriekAdjunction _ (𝟙 S))
  have hid : leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 S) ≪≫
      unboundedEtaleUpperStarIdIso A S = leftDerivedUpperStarId (ModuleCat.{u + 1} A) S := by
    simp only [leftDerivedUpperStarId, leftDerivedUpperStarIsoMapDerivedCategory,
      unboundedEtaleUpperStarIdIso, Functor.leftDerivedFunctorNatIso]
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  have hu : (etaleSumPullbackUnitIso A (𝟙 S)).hom =
      (unboundedEtaleUpperStarIdIso A S).hom.app (𝟙_ _) := by
    rw [etaleSumPullbackUnitIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
      ← derived_pullback_unit_id A S, ← hid]
    simp only [Iso.trans_hom, NatTrans.comp_app, constantComplex,
      Iso.inv_hom_id_app_assoc]
  simpa only [etaleSumRightAdjointUnitIso, Iso.trans_hom, Iso.app_hom,
    NatTrans.comp_app, hu, constantComplex] using congrArg (fun i ↦ i.hom.app (𝟙_ _)) h

/-- The identity-adjunction comparison for a rank-zero bundle is its normalized
etale section coordinate map.
Source: the third arrow of sk-prop-sp-orientation.proof.md in rank zero;
finite-ring bundle section orientation, Step 8.
(blueprint: lem-pur-rank-zero-bundle-section-coordinates).

Proof: the bundle zero section is the inverse of its structural isomorphism.
Use its Cartesian square over the identity to apply section-coordinate base
change. The normalized etale sum right adjoint on the identity has the canonical
identity-adjunction coordinates. The ordinary coefficient pullback equals the
monoidal unit pullback by ordinaryFiniteUnitPullback_eq_unitCoordinates.
After these substitutions, the naturality of the identity-pullback isomorphism
moves the section coordinates past the inverse identity constraint. The two
identity constraints cancel. All arguments are categorical and apply equally
to the empty base and zero coefficient ring. -/
theorem rankZeroBundleSection_coordinates
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S]
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank 0]
    [Etale (VectorBundleZeroSection.π S 0 M)]
    (e : VectorBundleZeroSection.scheme S 0 M ≅ S)
    (hz : e.inv = VectorBundleZeroSection.zero S 0 M)
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C) :
    bundleSectionRankZeroComparison A S M e hz =
      (finiteSmoothSectionCoordinates A C (VectorBundleZeroSection.π S 0 M)
        (VectorBundleZeroSection.zero S 0 M)).hom := by
  have : IsIso (VectorBundleZeroSection.zero S 0 M) := hz ▸ inferInstance
  let sq := IsPullback.of_horiz_isIso
    (CommSq.mk ((VectorBundleZeroSection.zero_spec S 0 M).1.trans
      (Category.comp_id _).symm))
  have hb := section_coordinates_baseChange A sq
    (VectorBundleZeroSection.zero S 0 M) (𝟙 S) rfl C hC
  have hid : (finiteSmoothSectionCoordinates A C (𝟙 S) (𝟙 S)).hom =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app _ ≫
        ((conjugateIsoEquiv
          (rightDerivedUpperShriekAdjunction A (𝟙 S))
          (Adjunction.id)) (unboundedEtaleLowerShriekId A S).symm).hom.app (𝟙_ _) := by
    dsimp only [finiteSmoothSectionCoordinates, Iso.trans_hom, Functor.mapIso_hom]
    rw [identity_omega_coordinates A S C hC, ← derived_pullback_unit_id A S]
    exact (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.naturality _
  dsimp only [bundleSectionRankZeroComparison, bundleSectionComparison,
    bundleSectionPullbackSquare]
  rw [ordinaryFiniteUnitPullback_eq_unitCoordinates]
  dsimp only [NoetherianSectionSpecialization.sectionMap, sectionInvariant,
    dualizingComplex, dualizingComplexBaseChangeMap, constantComplex] at hb
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  erw [← hid]
  simp only [Iso.app_hom, Iso.app_inv, Category.assoc] at hb ⊢
  erw [hb]
  rw [← derived_pullback_unit_id A S]
  have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.naturality
    (finiteSmoothSectionCoordinates A C (VectorBundleZeroSection.π S 0 M)
      (VectorBundleZeroSection.zero S 0 M)).hom
  dsimp only [ordinaryFinitePullback, sectionInvariant, dualizingComplex,
    bundleSectionOmega] at hn ⊢
  erw [← reassoc_of% hn]
  simp only [Iso.inv_hom_id_app]
  exact Category.comp_id _

end AlgebraicGeometry.Etale.FiniteSmoothPurity
