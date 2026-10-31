/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationTotalCounitMaps
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationOverlapChartPrefix

/-! # Exchange for the flattened simultaneous bundle chart

This comparison stops before any affine trace counit is applied.
(blueprint: lem-pur-vector-integration-total-counit-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek upperStar lowerStar
  VectorBundleZeroSection.π VectorBundleZeroSection.scheme
  leftDerivedUpperStarComp leftDerivedUpperStarIsoMapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory

/-- Pasting the specified exchanges compares the two prefixes by the coordinate action.
Source: vector-bundle purity, paragraph 2, simultaneous trivializations and linear invariance.
(blueprint: lem-pur-vector-integration-total-counit-exchange).

Proof: substitute c and ex. Apply compact-support exchange pasting horizontally to
sumIso followed by the flattened chart, and vertically to the two chart squares.
The vertical pasting gives `chartPrefix` followed by the affine compact-support
compositor. Naturality moves the total coefficient comparison through these
exchanges. Inverse-image associativity and normalized Tate pullback composition
identify it with `chartCoefficient` followed by `flattenCoefficient`. On the sum
side, the geometric equality hg identifies the chart with the linear substitution
and the rank-transported sum chart. The Cartesian-prefix action equation extracts
exactly `affineLinearTraceAction`. The bounded/unbounded compact comparisons
conjugate this action to the displayed affine source. Cancel the identity-pullback
comparisons and the invertible sumIso exchange. No projective-line datum or trace
is used. These equations also apply when either coordinate block has rank zero. -/
theorem vectorIntegration_totalCounit_exchange (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (V U : S.Opens) (eF : VectorBundleZeroSection.Trivialization S r F V)
    (eG : VectorBundleZeroSection.Trivialization S s G U)
    (W : S.Opens) [IsNoetherian W.toScheme] (hWV : W ≤ V) (hWU : W ≤ U) :
    letI := affineTraceNoetherian W.toScheme s
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
    ∀ (g : Matrix.GeneralLinearGroup (Fin (s + r)) Γ(W.toScheme, ⊤)),
    (VectorIntegrationDirectSumCounit.towerBlockIso W.toScheme s r).inv ≫
        VectorIntegrationDirectSumCounit.chart S r s F G V U eF eG W hWV hWU ≫
        (VectorTraceGeometry.sumIso S r s F G).hom =
      affineTraceLinearMap W.toScheme (s + r) g ≫
        eqToHom (congrArg (affineTraceTower W.toScheme) (Nat.add_comm s r)) ≫
        vectorIntegrationChart S (r + s) (VectorTraceGeometry.sum S F G) W
          (VectorIntegrationDirectSumCounit.sumFrame S r s F G V U eF eG W hWV hWU) →
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
      vectorIntegrationChartPrefix N hN A hA t S hS (r + s)
        (VectorTraceGeometry.sum S F G) W
        (VectorIntegrationDirectSumCounit.sumFrame S r s F G V U eF eG W hWV hWU) ≫
      eqToHom (congrArg (fun d ↦ (affineTraceLeft A W.toScheme d).obj
        ((affineTraceRight A N hA W.toScheme d).obj (ordinaryFiniteUnit A W.toScheme)))
        (Nat.add_comm r s)) ≫
      affineLinearTraceAction N hN A hA t W.toScheme
        (affineTracePullbackInvertible N W.ι hS) (s + r)
        (affineTraceLinearMap W.toScheme (s + r) g)
        (affineTraceLinearMap_isPullback W.toScheme (s + r) g) =
    VectorIntegrationTotalCounit.chartPrefix A N hA t S hS r s F G V U eF eG
      W hWV hWU ≫
      (unboundedEtaleLowerShriekCompIso A
        (affineTraceProjection (affineTraceTower W.toScheme s) r)
        (affineTraceProjection W.toScheme s)).hom.app _ ≫
      (affineLinearPullbackId A W.toScheme).inv.app _ ≫
      (rightDerivedLowerShriekBaseChangeMap A
        (VectorIntegrationTotalCounit.flattenSquare W.toScheme r s)).app _ ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection W.toScheme (s + r))).map
        (VectorIntegrationTotalCounit.flattenCoefficient A N hA t W.toScheme
          (affineTracePullbackInvertible N W.ι hS) r s).hom ≫
      (affineLinearCompactComparison N hN A hA W.toScheme
        (affineTracePullbackInvertible N W.ι hS) (s + r)).inv := by
  sorry

end AlgebraicGeometry.Etale
