/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitData
public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization.OrdinaryAffineCounitTensorMaps
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Equality of the canonical ordered source descents -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
open CategoryTheory.Limits
open scoped CategoryTheory.Functor

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
  AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  Etale.ordinaryFinitePullback._proof_1 Etale.ordinaryFinitePullback._proof_2
  Etale.ordinaryFinitePullback._proof_3 Etale.ordinaryFinitePullback._proof_4
  Etale.ordinaryFinitePullback._proof_5 Etale.ordinaryFinitePullback._proof_6
  Etale.ordinaryFinitePullback._proof_7 Etale.ordinaryFinitePullback._proof_8
  Etale.ordinaryFinitePullback._proof_9 Etale.ordinaryFinitePullback._proof_10
  Etale.ordinaryFinitePullback._proof_11 Etale.ordinaryFinitePullback._proof_12
  Etale.ordinaryFinitePullback._proof_13

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.finiteEtaleTateLine DerivedCategory.TStructure.t
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory DerivedCategory.singleFunctors

attribute [local implicit_reducible] affineTraceTower affineTraceProjection
  Etale.derivedTensorRight Etale.derivedTensorRightFunctor
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
end AlgebraicGeometry.ProEtale.AffineOrderedIntegration

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

private theorem descentStep_eq (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (Y : Scheme.{u}) (hY : IsUnit (N : Γ(Y, ⊤)))
    (K : Etale.DerivedCategoryModule A Y) (d : ℕ)
    (e : (Etale.affineTraceRight A N hA Y d).obj K ≅
      (Etale.ordinaryFinitePullback A (affineTraceProjection Y d)).obj
        (((Etale.ordinaryFiniteTensor A Y).obj K).obj
          (Etale.affineLinearBaseCoefficient A N hA Y d))) :
    Etale.OrdinaryAffineCounitTensorNormalization.descentStep A N hA t Y hY d K e =
      ordinaryDescentStepRaw A N hA t Y hY K d e := by
  apply Iso.ext
  simp only [Etale.OrdinaryAffineCounitTensorNormalization.descentStep,
    ordinaryDescentStepRaw, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Iso.symm_hom, Iso.app_hom, Category.assoc]
  have hn := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace PUnit.{u + 1} (affineTraceTower Y d) ↘ affineTraceTower Y d)
    (affineTraceProjection Y d)).inv.naturality
      (Etale.derivedTensorAssociator (ModuleCat.{u + 1} A) Y K
        (Etale.affineLinearBaseCoefficient A N hA Y d)
        ((Etale.ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧)).hom
  dsimp only [Functor.comp_map] at hn
  simpa only [Etale.ordinaryFiniteTensor, Etale.ordinaryFinitePullback,
    Etale.affineLinearBaseCoefficient, Etale.derivedTensorRight,
    Functor.flip_obj_obj, affineTraceProjection] using
    congrArg (fun m ↦
      (Etale.affineLinearLineDescent A N hA t (affineTraceTower Y d)
        (affineTraceInvertible N Y hY d) _).hom ≫
        (Etale.ordinaryFinitePullback A
          (AffineSpace PUnit.{u + 1} (affineTraceTower Y d) ↘ affineTraceTower Y d)).map
          (Etale.ordinaryFiniteTensorRightMapIso A (affineTraceTower Y d) e
            (Etale.ordinaryFiniteShiftedLinePullback A N hA t
              (affineTraceProjection Y d) hY).symm).hom ≫
        (Etale.ordinaryFinitePullback A
          (AffineSpace PUnit.{u + 1} (affineTraceTower Y d) ↘ affineTraceTower Y d)).map
          (Etale.ordinaryFiniteTensorPullback A (affineTraceProjection Y d)
            (((Etale.ordinaryFiniteTensor A Y).obj K).obj
              (Etale.affineLinearBaseCoefficient A N hA Y d))
            ((Etale.ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧)).inv ≫ m) hn.symm

private theorem descentZero_eq (A : Type (u + 1)) [CommRing A]
    (Y : Scheme.{u}) (K : Etale.DerivedCategoryModule A Y) :
    (Etale.derivedTensorSingleUnitIso K).symm ≪≫
        ((Etale.affineLinearPullbackId A Y).app _).symm =
      ordinaryDescentZeroRaw A Y K := by
  apply Iso.ext
  simp only [ordinaryDescentZeroRaw, identityPullbackSource, Iso.trans_hom,
    Iso.symm_hom, asIso_inv]
  congr 1
  have h := Etale.ordinaryFiniteTensorTrace_app A Y (𝟙 (Etale.ordinaryFiniteUnit A Y)) K
  rw [((Etale.ordinaryFiniteTensor A Y).obj K).map_id, Category.id_comp] at h
  let _ := ordinaryZeroTensorTrace_isIso A Y K
  have he : asIso ((Etale.ordinaryFiniteTensorTrace A Y
      (𝟙 (Etale.ordinaryFiniteUnit A Y))).app K) =
      Etale.derivedTensorSingleUnitIso K := Iso.ext h
  exact (congrArg Iso.inv he).symm

/-- The canonical source descent equals the normalized ordered tensor descent.
Source: the recursion clauses for ordinarySourceDescent and the ordered affine tensor
reassociation, in the affine-space coefficient-counit calculation.
(blueprint: lem-pur-affine-ordered-counit-descent-comparison).

Proof: at zero the tensor trace at the identity is the right unitor, hence its inverse
is the inverse right unitor. In a successor clause, naturality of the inverse
pullback-composition comparison moves the tensor associator through the comparison.
Thus the two recursions have equal zero and successor maps. Induction, using the
specified recursion property of ordinarySourceDescent, identifies their components. -/
theorem normalized_source_descent (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (Y : Scheme.{u}) (hY : IsUnit (N : Γ(Y, ⊤)))
    (K : Etale.DerivedCategoryModule A Y) (d : ℕ) :
    Etale.OrdinaryAffineCounitTensorNormalization.descent A N hA t Y hY d K =
      ordinarySourceDescent A N hA t Y hY K d := by
  have hs := (ordinarySourceDescent_existsUnique A N hA t Y hY K).exists.choose_spec
  induction d with
  | zero =>
    apply Iso.ext
    change ((Etale.derivedTensorSingleUnitIso K).symm ≪≫
      ((Etale.affineLinearPullbackId A Y).app _).symm).hom = _
    exact (congrArg Iso.hom (descentZero_eq A Y K)).trans (eq_of_heq hs.1).symm
  | succ d ih =>
    apply Iso.ext
    change (Etale.OrdinaryAffineCounitTensorNormalization.descentStep A N hA t Y hY d K
      (Etale.OrdinaryAffineCounitTensorNormalization.descent A N hA t Y hY d K)).hom = _
    rw [ih, descentStep_eq]
    exact (eq_of_heq (hs.2 d)).symm

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
