/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationCartesianPrefix
public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction

/-! # The two-block affine counit on a simultaneous frame open

Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2. The reference arrow uses the s-coordinate counit after the r-coordinate
counit. Neither integration arrow to be compared occurs in its construction.
(blueprint: def-pur-vector-integration-direct-sum-counit-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
namespace VectorIntegrationDirectSumCounit

attribute [local irreducible] rightDerivedLowerShriek upperStar
  VectorBundleZeroSection.π VectorBundleZeroSection.scheme
  leftDerivedUpperStarComp derivedSquareUpperStarIso
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory

section Geometry
variable (S : Scheme.{u}) [IsNoetherian S] (r s : ℕ)
  (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
  (V U : S.Opens) (eF : VectorBundleZeroSection.Trivialization S r F V)
  (eG : VectorBundleZeroSection.Trivialization S s G U)
  (W : S.Opens) (hWV : W ≤ V) (hWU : W ≤ U)

/-- The outer square before lifting to the pulled-back fibre bundle.
Proof: paste the affine-tower base-change square with the restricted F-chart square,
then use the restricted G-chart's structural equation.
Source: vector-bundle purity proof, simultaneous frames, paragraph 2.
(blueprint: def-pur-vector-integration-direct-sum-counit-maps). -/
theorem outerSquare :
    IsPullback
      (affineTraceMap (affineTraceProjection W.toScheme s) r ≫
        vectorIntegrationRestrictedChart S r F W V hWV eF)
      (affineTraceProjection (affineTraceTower W.toScheme s) r)
      (VectorBundleZeroSection.π S r F)
      (vectorIntegrationRestrictedChart S s G W U hWU eG ≫
        VectorBundleZeroSection.π S s G) := by
  rw [(vectorIntegrationRestrictedChart_isPullback S s G W U hWU eG).w]
  exact (affineTraceMap_isPullback (affineTraceProjection W.toScheme s) r).paste_horiz
    (vectorIntegrationRestrictedChart_isPullback S r F W V hWV eF)

/-- The simultaneous double chart, constructed by the Cartesian universal property.
Source: vector-bundle purity proof, simultaneous frames, paragraph 2.
(blueprint: def-pur-vector-integration-direct-sum-counit-maps). -/
def chart : affineTraceTower (affineTraceTower W.toScheme s) r ⟶
    VectorBundleZeroSection.scheme (VectorBundleZeroSection.scheme S s G) r
      ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F) :=
  (VectorTraceGeometry.baseChange_isPullback (VectorBundleZeroSection.π S s G) r F).lift
    (affineTraceMap (affineTraceProjection W.toScheme s) r ≫
      vectorIntegrationRestrictedChart S r F W V hWV eF)
    (affineTraceProjection (affineTraceTower W.toScheme s) r ≫
      vectorIntegrationRestrictedChart S s G W U hWU eG)
    (by rw [(outerSquare S r s F G V U eF eG W hWV hWU).w, Category.assoc])

/-- The inner double-chart square is Cartesian by cancellation of Cartesian squares.
Source: vector-bundle purity proof, simultaneous frames, paragraph 2.
Proof: cancel the canonical fibre-bundle base-change square from outerSquare.
(blueprint: def-pur-vector-integration-direct-sum-counit-maps). -/
theorem chart_isPullback :
    IsPullback (chart S r s F G V U eF eG W hWV hWU)
      (affineTraceProjection (affineTraceTower W.toScheme s) r)
      (VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F))
      (vectorIntegrationRestrictedChart S s G W U hWU eG) :=
  IsPullback.of_right' (outerSquare S r s F G V U eF eG W hWV hWU)
    (VectorTraceGeometry.baseChange_isPullback (VectorBundleZeroSection.π S s G) r F)

/-- The total double-chart square obtained by vertical pasting.
Source: vector-bundle purity proof, simultaneous frames, paragraph 2.
Proof: paste chart_isPullback with the restricted G-chart square.
(blueprint: def-pur-vector-integration-direct-sum-counit-maps). -/
theorem totalSquare :
    IsPullback (chart S r s F G V U eF eG W hWV hWU)
      (affineTraceProjection (affineTraceTower W.toScheme s) r ≫
        affineTraceProjection W.toScheme s)
      (VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F) ≫
        VectorBundleZeroSection.π S s G) W.ι :=
  (chart_isPullback S r s F G V U eF eG W hWV hWU).paste_vert
    (vectorIntegrationRestrictedChart_isPullback S s G W U hWU eG)
end Geometry

/-- One ordered reassociation step, with an arbitrary unbounded coefficient input.
Source: affine-space top trace proof, ordered coordinate tower
(blueprint: def-pur-vector-integration-direct-sum-counit-maps). -/
def coefficientDescentStep (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (K : DerivedCategoryModule A S)
    (e : (affineTraceRight A N hA S d).obj K ≅
      (ordinaryFinitePullback A (affineTraceProjection S d)).obj
        (((ordinaryFiniteTensor A S).obj K).obj (affineLinearBaseCoefficient A N hA S d))) :
    (affineTraceLineRight A N hA (affineTraceTower S d)).obj
        ((affineTraceRight A N hA S d).obj K) ≅
      (ordinaryFinitePullback A (affineTraceProjection S (d + 1))).obj
        (((ordinaryFiniteTensor A S).obj K).obj
          (affineLinearBaseCoefficient A N hA S (d + 1))) :=
  affineLinearLineDescent A N hA t (affineTraceTower S d)
      (affineTraceInvertible N S hS d) ((affineTraceRight A N hA S d).obj K) ≪≫
    (ordinaryFinitePullback A
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)).mapIso
      (ordinaryFiniteTensorRightMapIso A (affineTraceTower S d) e
        (ordinaryFiniteShiftedLinePullback A N hA t (affineTraceProjection S d) hS).symm ≪≫
      (ordinaryFiniteTensorPullback A (affineTraceProjection S d)
        (((ordinaryFiniteTensor A S).obj K).obj (affineLinearBaseCoefficient A N hA S d))
        ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).symm) ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (affineTraceProjection S d)).symm.app _ ≪≫
    (ordinaryFinitePullback A (affineTraceProjection S (d + 1))).mapIso
      (derivedTensorAssociator (ModuleCat.{u + 1} A) S K
        (affineLinearBaseCoefficient A N hA S d)
        ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧))

/-- Canonical ordered descent for every complex, extending the coefficient descent.
Source: affine-space top trace proof, ordered coordinate tower
(blueprint: def-pur-vector-integration-direct-sum-counit-maps). -/
def coefficientDescent (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (K : DerivedCategoryModule A S) :
    (affineTraceRight A N hA S d).obj K ≅
      (ordinaryFinitePullback A (affineTraceProjection S d)).obj
        (((ordinaryFiniteTensor A S).obj K).obj (affineLinearBaseCoefficient A N hA S d)) :=
  Nat.rec (motive := fun e ↦ (affineTraceRight A N hA S e).obj K ≅
      (ordinaryFinitePullback A (affineTraceProjection S e)).obj
        (((ordinaryFiniteTensor A S).obj K).obj (affineLinearBaseCoefficient A N hA S e)))
    ((derivedTensorSingleUnitIso K).symm ≪≫
      ((affineLinearPullbackId A S).app _).symm)
    (fun e r ↦ coefficientDescentStep A N hA t S hS e K r) d

/-- The right-adjoint coefficient comparison for two blocks, with base coordinates first.
Source: vector-bundle purity proof, ordered Tate products, paragraph 2.
(blueprint: def-pur-vector-integration-direct-sum-counit-maps). -/
def rightCoefficient (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (r s : ℕ) :
    (affineTraceRight A N hA (affineTraceTower T s) r).obj
      ((affineTraceRight A N hA T s).obj (ordinaryFiniteUnit A T)) ≅
    (ordinaryFinitePullback A
      (affineTraceProjection (affineTraceTower T s) r ≫ affineTraceProjection T s)).obj
      (affineLinearBaseCoefficient A N hA T (r + s)) :=
  coefficientDescent A N hA t (affineTraceTower T s)
      (affineTraceInvertible N T hT s) r
      ((affineTraceRight A N hA T s).obj (ordinaryFiniteUnit A T)) ≪≫
    (ordinaryFinitePullback A (affineTraceProjection (affineTraceTower T s) r)).mapIso
      (ordinaryFiniteTensorRightMapIso A (affineTraceTower T s)
        (affineLinearCoefficientDescent A N hA t T hT s)
        (vectorIntegrationBaseCoefficientPullback A N hA t
          (affineTraceProjection T s) hT r).symm ≪≫
        (ordinaryFiniteTensorPullback A (affineTraceProjection T s)
          (affineLinearBaseCoefficient A N hA T s)
          (affineLinearBaseCoefficient A N hA T r)).symm) ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (affineTraceProjection (affineTraceTower T s) r)
      (affineTraceProjection T s)).symm.app _ ≪≫
    (ordinaryFinitePullback A
      (affineTraceProjection (affineTraceTower T s) r ≫ affineTraceProjection T s)).mapIso
      (eqToIso (congrArg (affineLinearBaseCoefficient A N hA T) (Nat.add_comm r s)) ≪≫
        WeilConjectures.PurityFiniteSetting.purityPowerAdd A N hA T s r).symm

/-- The genuine composite adjunction for the r coordinates over the s-coordinate base.
Source: vector-bundle purity proof, ordered affine counits, paragraph 2.
(blueprint: def-pur-vector-integration-direct-sum-counit-maps). -/
def blockAdjunction (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))) (r s : ℕ) :
    (affineTraceLeft A (affineTraceTower T s) r ⋙ affineTraceLeft A T s) ⊣
      (affineTraceRight A N hA T s ⋙ affineTraceRight A N hA (affineTraceTower T s) r) := by
  letI := affineTraceNoetherian T s
  exact (affineTraceAdjunction A N hA t D (affineTraceTower T s)
    (affineTraceInvertible N T hT s) r).comp (affineTraceAdjunction A N hA t D T hT s)

section Counit
variable (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
  (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
  (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
    OrdinaryFiniteP1Datum A N hA t T hT)
  (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
  (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
  (V U : S.Opens) (eF : VectorBundleZeroSection.Trivialization S r F V)
  (eG : VectorBundleZeroSection.Trivialization S s G U)
  (W : S.Opens) [IsNoetherian W.toScheme] (hWV : W ≤ V) (hWU : W ≤ U)

/-- The coefficient pulled through the total Cartesian square, in two-block normal form.
Source: vector-bundle purity proof, coefficient normalization, paragraph 2.
(blueprint: def-pur-vector-integration-direct-sum-counit-maps). -/
def coefficient :
    (ordinaryFinitePullback A (chart S r s F G V U eF eG W hWV hWU)).obj
      ((ordinaryFinitePullback A
        (VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
          ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F) ≫
          VectorBundleZeroSection.π S s G)).obj
        (affineLinearBaseCoefficient A N hA S (r + s))) ≅
    (affineTraceRight A N hA (affineTraceTower W.toScheme s) r).obj
      ((affineTraceRight A N hA W.toScheme s).obj (ordinaryFiniteUnit A W.toScheme)) :=
  (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
      (totalSquare S r s F G V U eF eG W hWV hWU).toCommSq).symm.app _ ≪≫
    (ordinaryFinitePullback A
      (affineTraceProjection (affineTraceTower W.toScheme s) r ≫
        affineTraceProjection W.toScheme s)).mapIso
      (vectorIntegrationBaseCoefficientPullback A N hA t W.ι hS (r + s)) ≪≫
    (rightCoefficient A N hA t W.toScheme
      (affineTracePullbackInvertible N W.ι hS) r s).symm

/-- An actual reference arrow: exchange twice, transport the coefficient, then apply
first the r-block counit and then the s-block counit. No bundle integration is used.
Source: vector-bundle purity proof, ordered composite counit, paragraph 2.
(blueprint: def-pur-vector-integration-direct-sum-counit-maps). -/
def counit :
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
    ordinaryFiniteUnit A W.toScheme := by
  letI := affineTraceNoetherian W.toScheme s
  let hW := affineTracePullbackInvertible N W.ι hS
  let qs := affineTraceProjection W.toScheme s
  let qr := affineTraceProjection (affineTraceTower W.toScheme s) r
  let RsUnit := (affineTraceRight A N hA W.toScheme s).obj
    (ordinaryFiniteUnit A W.toScheme)
  exact (rightDerivedLowerShriekBaseChangeMap A
      (vectorIntegrationRestrictedChart_isPullback S s G W U hWU eG)).app _ ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) qs).map
      ((rightDerivedLowerShriekBaseChangeMap A
          (chart_isPullback S r s F G V U eF eG W hWV hWU)).app _ ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) qr).map
          (coefficient N A hA t S hS r s F G V U eF eG W hWV hWU).hom ≫
        (affineTraceUnboundedCompactComparison A (affineTraceTower W.toScheme s) r).inv.app
          ((affineTraceRight A N hA (affineTraceTower W.toScheme s) r).obj RsUnit)) ≫
    (affineTraceUnboundedCompactComparison A W.toScheme s).inv.app _ ≫
    (blockAdjunction A N hA t D W.toScheme hW r s).counit.app
      (ordinaryFiniteUnit A W.toScheme)
end Counit
end VectorIntegrationDirectSumCounit
end AlgebraicGeometry.Etale
