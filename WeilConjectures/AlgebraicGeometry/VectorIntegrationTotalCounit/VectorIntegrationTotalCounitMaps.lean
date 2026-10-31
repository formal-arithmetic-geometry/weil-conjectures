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

/-- The inverse flattening is Cartesian over the identity on the base.
Source: vector-bundle purity proof, paragraph 2, simultaneous coordinates.
(blueprint: def-pur-vector-integration-total-counit-comparison).
Proof: flattening is an isomorphism and its structural equation is towerBlockIso_over. -/
theorem flattenSquare (T : Scheme.{u}) (r s : ℕ) :
    IsPullback (VectorIntegrationDirectSumCounit.towerBlockIso T s r).inv
      (affineTraceProjection T (s + r))
      (affineTraceProjection (affineTraceTower T s) r ≫ affineTraceProjection T s)
      (𝟙 T) := by
  apply IsPullback.of_horiz_isIso
  constructor
  rw [← VectorIntegrationDirectSumCounit.towerBlockIso_over, Iso.inv_hom_id_assoc,
    Category.comp_id]

/-- Canonical coefficient comparison for inverse flattening. Rank commutation here is
an equality of natural numbers; no tensor symmetry or choice of orientation is inserted.
Source: vector-bundle purity proof, paragraph 2, additive twists.
(blueprint: def-pur-vector-integration-total-counit-comparison). -/
def flattenCoefficient (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (r s : ℕ) :
    (ordinaryFinitePullback A
      (VectorIntegrationDirectSumCounit.towerBlockIso T s r).inv).obj
      ((ordinaryFinitePullback A
        (affineTraceProjection (affineTraceTower T s) r ≫ affineTraceProjection T s)).obj
        (affineLinearBaseCoefficient A N hA T (r + s))) ≅
    (affineTraceRight A N hA T (s + r)).obj (ordinaryFiniteUnit A T) :=
  (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
      (flattenSquare T r s).toCommSq).symm.app _ ≪≫
    (ordinaryFinitePullback A (affineTraceProjection T (s + r))).mapIso
      ((affineLinearPullbackId A T).app _ ≪≫
        eqToIso (congrArg (affineLinearBaseCoefficient A N hA T) (Nat.add_comm r s))) ≪≫
    (affineLinearCoefficientDescent A N hA t T hT (s + r)).symm

/-- Trace on the flattened tower, before identifying it with the two-block adjunction.
It is the actual single affine trace transported by the explicit inverse flattening.
Source: vector-bundle purity proof, paragraph 2, ordered affine-space counit.
(blueprint: def-pur-vector-integration-total-counit-comparison). -/
def flattenedTrace (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))) (r s : ℕ) :
    letI := affineTraceNoetherian T s
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection (affineTraceTower T s) r ≫ affineTraceProjection T s)).obj
      ((ordinaryFinitePullback A
        (affineTraceProjection (affineTraceTower T s) r ≫ affineTraceProjection T s)).obj
        (affineLinearBaseCoefficient A N hA T (r + s))) ⟶ ordinaryFiniteUnit A T := by
  letI := affineTraceNoetherian T s
  exact (affineLinearPullbackId A T).inv.app _ ≫
    (rightDerivedLowerShriekBaseChangeMap A (flattenSquare T r s)).app _ ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection T (s + r))).map
      (flattenCoefficient A N hA t T hT r s).hom ≫
    (affineLinearCompactComparison N hN A hA T hT (s + r)).inv ≫
    affineTraceCounit A N hA t D T hT (s + r)

/-- The prefix of the two-block counit starting with descended coefficients.
This consists only of coefficient descent and the two unbounded compact comparisons.
Source: vector-bundle purity proof, paragraph 2, ordered affine counits.
(blueprint: def-pur-vector-integration-total-counit-comparison). -/
def blockPrefix (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (r s : ℕ) :
    letI := affineTraceNoetherian T s
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection T s)).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection (affineTraceTower T s) r)).obj
        ((ordinaryFinitePullback A
          (affineTraceProjection (affineTraceTower T s) r ≫ affineTraceProjection T s)).obj
          (affineLinearBaseCoefficient A N hA T (r + s)))) ⟶
    (affineTraceLeft A T s).obj
      ((affineTraceLeft A (affineTraceTower T s) r).obj
        ((affineTraceRight A N hA (affineTraceTower T s) r).obj
          ((affineTraceRight A N hA T s).obj (ordinaryFiniteUnit A T)))) := by
  letI := affineTraceNoetherian T s
  exact (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection T s)).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (affineTraceProjection (affineTraceTower T s) r)).map
          (VectorIntegrationDirectSumCounit.rightCoefficient A N hA t T hT r s).inv ≫
        (affineTraceUnboundedCompactComparison A (affineTraceTower T s) r).inv.app _) ≫
    (affineTraceUnboundedCompactComparison A T s).inv.app _

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

/-- Exchange for the two chart squares, followed by descent to the total coefficient
on W. The codomain has compact supports of both blocks and contains no counit.
Source: vector-bundle purity proof, paragraph 2, simultaneous chart exchange.
(blueprint: def-pur-vector-integration-total-counit-comparison). -/
def chartPrefix :
    letI := affineTraceNoetherian W.toScheme s
    (ordinaryFinitePullback A W.ι).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S s G)).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
            ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F))).obj
          ((ordinaryFinitePullback A
            (VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
              ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F) ≫
                VectorBundleZeroSection.π S s G)).obj
            (affineLinearBaseCoefficient A N hA S (r + s))))) ⟶
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection W.toScheme s)).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection (affineTraceTower W.toScheme s) r)).obj
        ((ordinaryFinitePullback A
          (affineTraceProjection (affineTraceTower W.toScheme s) r ≫
            affineTraceProjection W.toScheme s)).obj
          (affineLinearBaseCoefficient A N hA W.toScheme (r + s)))) := by
  letI := affineTraceNoetherian W.toScheme s
  exact (rightDerivedLowerShriekBaseChangeMap A
      (vectorIntegrationRestrictedChart_isPullback S s G W U hWU eG)).app _ ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection W.toScheme s)).map
      ((rightDerivedLowerShriekBaseChangeMap A
        (VectorIntegrationDirectSumCounit.chart_isPullback
          S r s F G V U eF eG W hWV hWU)).app _ ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (affineTraceProjection (affineTraceTower W.toScheme s) r)).map
          (chartCoefficient A N hA t S hS r s F G V U eF eG W hWV hWU).hom)

end Charts
end VectorIntegrationTotalCounit
end AlgebraicGeometry.Etale
