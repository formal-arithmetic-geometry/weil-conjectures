/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationDirectSumCounit.VectorIntegrationDirectSumCounitMaps

/-! # The flattened affine trace between the two direct-sum comparisons

The coordinate tower has the s base coordinates followed by r fibre coordinates.
Its trace is defined using the existing rank-(s+r) affine trace and the explicit
flattening isomorphism. It contains no two-block adjunction counit.
(blueprint: def-pur-vector-integration-total-counit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
namespace VectorIntegrationTotalCounit

attribute [local irreducible] rightDerivedLowerShriek upperStar lowerStar
  VectorBundleZeroSection.π VectorBundleZeroSection.scheme leftDerivedUpperStarComp
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory

section Charts
variable (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
  (t : OrdinaryFiniteTwistTransport A N hA)
  (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
  (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
  (V U : S.Opens) (eF : VectorBundleZeroSection.Trivialization S r F V)
  (eG : VectorBundleZeroSection.Trivialization S s G U)
  (W : S.Opens) [IsNoetherian W.toScheme] (hWV : W ≤ V) (hWU : W ≤ U)

/-- Pull the total descended coefficient through the double chart, before identifying
it with the two right-adjoint blocks. No affine counit is involved.
Source: vector-bundle purity proof, paragraph 2, coefficient pullback.
(blueprint: def-pur-vector-integration-total-counit-comparison). -/
def chartCoefficient :
    (ordinaryFinitePullback A
      (VectorIntegrationDirectSumCounit.chart S r s F G V U eF eG W hWV hWU)).obj
      ((ordinaryFinitePullback A
        (VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
          ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F) ≫
            VectorBundleZeroSection.π S s G)).obj
        (affineLinearBaseCoefficient A N hA S (r + s))) ≅
    (ordinaryFinitePullback A
      (affineTraceProjection (affineTraceTower W.toScheme s) r ≫
        affineTraceProjection W.toScheme s)).obj
      (affineLinearBaseCoefficient A N hA W.toScheme (r + s)) :=
  (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
    (VectorIntegrationDirectSumCounit.totalSquare
      S r s F G V U eF eG W hWV hWU).toCommSq).symm.app _ ≪≫
    (ordinaryFinitePullback A
      (affineTraceProjection (affineTraceTower W.toScheme s) r ≫
        affineTraceProjection W.toScheme s)).mapIso
      (vectorIntegrationBaseCoefficientPullback A N hA t W.ι hS (r + s))

end Charts
end VectorIntegrationTotalCounit
end AlgebraicGeometry.Etale
