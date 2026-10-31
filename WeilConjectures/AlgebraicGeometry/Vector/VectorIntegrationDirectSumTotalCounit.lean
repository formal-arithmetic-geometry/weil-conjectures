/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationDirectSumCounit.VectorIntegrationDirectSumCounitMaps
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationTotalCounitGeometric
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationTotalCounitAffine

/-! # Sum-frame trace in two coordinate blocks

Source: blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, simultaneous trivializations.
(blueprint: lem-pur-vector-integration-direct-sum-total-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

attribute [local irreducible] AlgebraicGeometry.Etale.rightDerivedLowerShriek
  AlgebraicGeometry.Etale.upperStar AlgebraicGeometry.Etale.lowerStar
  AlgebraicGeometry.VectorBundleZeroSection.π AlgebraicGeometry.VectorBundleZeroSection.scheme
  AlgebraicGeometry.Etale.leftDerivedUpperStarComp
  AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
namespace AlgebraicGeometry.Etale

attribute [local irreducible] _root_.DerivedCategory.singleFunctors
  unboundedEtaleLowerShriekId affineLinearPullbackId
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensorSymmetry projectionMapOfCompactification

set_option linter.unusedVariables false in
/-- The transported sum integration has the ordered two-block affine counit as its
normal form on a simultaneous frame open. The sum integration has already been replaced
by its prescribed local trace on the explicit biproduct frame;
there is no coefficient-first projection formula or iterated bundle integration here.
Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2, ordered affine counits and simultaneous trivializations.
(blueprint: lem-pur-vector-integration-direct-sum-total-counit).

Proof: restrict both frames to W and take their biproduct frame. Its inverse chart
is the product chart induced by the symmetric-algebra universal property, followed
by sumIso. Flatten the two affine coordinate blocks by the corresponding ordered
coordinate isomorphism. The explicit generator equations identify this with the
biproduct frame up to the permutation putting the s base coordinates first.
Expand the prescribed local trace on this frame. Linear trace invariance removes
the permutation. Expand the ordered affine adjunction at the cut after s coordinates;
its counit is the s-block counit following the mapped r-block counit. The normalized
compact-support compositor associates the two left block functors. Exchange pasting
through the product square gives exactly ex, and inverse-image compositor coherence
gives c and the coefficient comparison in the reference arrow. The coefficient
identity is proved by induction on r using tensor pullback associativity, the
normalized shifted Tate-line pullback composition law, and purityPowerAdd. Naturality
moves these coefficient comparisons through exchange. Cancel consecutive comparison
isomorphisms to obtain the displayed normal form. At rank zero the cut uses the
identity adjunction and its unit coherence; no positivity or nonempty-open argument
is needed.
-/
theorem vectorIntegration_directSum_total_counit (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (V U : S.Opens) (eF : VectorBundleZeroSection.Trivialization S r F V)
    (eG : VectorBundleZeroSection.Trivialization S s G U)
    (W : S.Opens) [IsNoetherian W.toScheme] (hWV : W ≤ V) (hWU : W ≤ U) :
    let fibre :=
      (Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F;
    let q :=
      VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
      (fibre);
    let h :=
      q ≫ VectorBundleZeroSection.π S s G;
    let Wh :=
      (ordinaryFinitePullback A (h)).obj
      (affineLinearBaseCoefficient A N hA S (r + s));
    ∀ (c : (ordinaryFinitePullback A (VectorTraceGeometry.sumIso S r s F G).hom).obj
        (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G)) ≅ Wh)
      (hc : c =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (VectorTraceGeometry.sumIso S r s F G).hom
      (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))
      (h)
      (by simpa only [Category.comp_id] using
        (VectorTraceGeometry.sumIso_isPullback S r s F G).w.symm)).symm.app _),
    ∀ (ex : (ordinaryFinitePullback A (𝟙 S)).obj
        (vectorIntegrationSource A N hA S (r + s) (VectorTraceGeometry.sum S F G)) ≅
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).obj
        ((ordinaryFinitePullback A (VectorTraceGeometry.sumIso S r s F G).hom).obj
          (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G))))
      (hex : ex = (by
      have hex := (unboundedEtaleCompactSupport_baseChange A
        (VectorTraceGeometry.sumIso_isPullback S r s F G)).1
      have hexa := @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hex
        (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G))
      exact (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 S)).app _ ≪≫
        @asIso _ _ _ _ ((unboundedEtaleCompactSupportBaseChange A
          (VectorTraceGeometry.sumIso_isPullback S r s F G)).app
          (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G)))
          hexa ≪≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
            (VectorTraceGeometry.sumIso S r s F G).hom).symm.app _))),
    let kh :=
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (h)).map
        (c).inv ≫
      (ex).inv ≫
      (affineLinearPullbackId A S).hom.app _;
    (ordinaryFinitePullback A W.ι).map
      ((unboundedEtaleLowerShriekCompIso A (q)
        (VectorBundleZeroSection.π S s G)).hom.app
        (Wh) ≫
      kh) ≫
      vectorIntegrationLocalTrace N hN A hA t D S hS (r + s)
        (VectorTraceGeometry.sum S F G) W
        (VectorIntegrationDirectSumCounit.sumFrame S r s F G V U eF eG W hWV hWU) =
    VectorIntegrationDirectSumCounit.counit N A hA t D S hS r s F G V U eF eG
      W hWV hWU := by
  let := affineTraceNoetherian W.toScheme s
  dsimp only
  intro c hc ex hex
  rw [vectorIntegration_totalCounit_geometric N hN A hA t D S hS r s F G
    V U eF eG W hWV hWU c hc ex hex]
  rw [vectorIntegration_totalCounit_affine N hN A hA t D W.toScheme
    (affineTracePullbackInvertible N W.ι hS) r s]
  simp only [VectorIntegrationTotalCounit.chartPrefix,
    VectorIntegrationTotalCounit.blockPrefix,
    VectorIntegrationDirectSumCounit.counit, VectorIntegrationDirectSumCounit.coefficient,
    VectorIntegrationTotalCounit.chartCoefficient,
    Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]


end AlgebraicGeometry.Etale
