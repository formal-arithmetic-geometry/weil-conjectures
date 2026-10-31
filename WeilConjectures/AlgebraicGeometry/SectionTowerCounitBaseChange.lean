/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows
public import WeilConjectures.AlgebraicGeometry.VectorBundleIntegrationCharts
import WeilConjectures.AlgebraicGeometry.SectionCoordinateCounitNormalization
import WeilConjectures.AlgebraicGeometry.VectorIntegrationRestrictedChartCoefficientCore
import WeilConjectures.AlgebraicGeometry.SectionPullbackCoefficientNaturality

/-! # Base change of the ordered tower orientation along sections -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  rightDerivedUpperShriek rightDerivedUpperShriekAdjunction
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem towerCoefficientAdjoint_baseChange (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (ordinaryFinitePullback A (affineTraceMap f d)).map
        ((affineLinearCoefficientDescent A N hA t S hS d).inv ≫
          CoordinateCounitArrows.towerAdjoint N hN A hA t D S hS d) ≫
      dualizingComplexBaseChangeMap A (affineTraceMap_isPullback f d) =
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (affineTraceMap_isPullback f d).toCommSq).inv.app
        (affineLinearBaseCoefficient A N hA S d) ≫
      (ordinaryFinitePullback A (affineTraceProjection T d)).map
        (vectorIntegrationBaseCoefficientPullback A N hA t f hS d).hom ≫
      (affineLinearCoefficientDescent A N hA t T
        (affineTracePullbackInvertible N f hS) d).inv ≫
      CoordinateCounitArrows.towerAdjoint N hN A hA t D T
        (affineTracePullbackInvertible N f hS) d := by
  have hc := congrArg Iso.hom (affineTraceRightBaseChange_unit_coefficient A N hA t f hS
    (affineTracePullbackInvertible N f hS) d)
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom] at hc
  simp only [Functor.map_comp, Category.assoc]
  rw [(affineCoordinateCounit_baseChange N hN A hA t D S hS d).2 T f]
  rw [reassoc_of% hc]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    Functor.map_id, Category.id_comp]
  rw [(ordinaryFinitePullback A (affineTraceMap f d)).map_id, Category.id_comp]

/-- The ordered tower counit adjunct commutes with base change after restriction
along any compatible sections. Source: orientation-charts Step 3.
(blueprint: lem-trf-section-tower-counit-base-change).
Proof: combine the counit adjunct base-change equation with the unit coefficient
descent equation. Cancel the descent isomorphism, then apply section pullback
coefficient naturality to the resulting ambient square. The section compositors
are precisely those in that naturality theorem. This also applies to the identity
tower in rank zero, arbitrary compatible sections, empty bases and the zero ring. -/
theorem coordinateTowerSection_baseChange (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (z : S ⟶ affineTraceTower S d) (z' : T ⟶ affineTraceTower T d)
    (h₀ : z ≫ affineTraceProjection S d = 𝟙 S)
    (h₁ : z' ≫ affineTraceProjection T d = 𝟙 T)
    (hz : z' ≫ affineTraceMap f d = f ≫ z) :
    (ordinaryFinitePullback A f).map
        ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z
          (affineTraceProjection S d) h₀).inv.app _ ≫
        (ordinaryFinitePullback A z).map
          ((affineLinearCoefficientDescent A N hA t S hS d).inv ≫
            CoordinateCounitArrows.towerAdjoint N hN A hA t D S hS d)) ≫
      SectionComparisonArrows.sectionMap A (affineTraceProjection S d)
        (affineTraceProjection T d) f (affineTraceMap f d)
        (affineTraceMap_isPullback f d) z z' hz =
    (vectorIntegrationBaseCoefficientPullback A N hA t f hS d).hom ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z'
        (affineTraceProjection T d) h₁).inv.app _ ≫
      (ordinaryFinitePullback A z').map
        ((affineLinearCoefficientDescent A N hA t T
          (affineTracePullbackInvertible N f hS) d).inv ≫
          CoordinateCounitArrows.towerAdjoint N hN A hA t D T
            (affineTracePullbackInvertible N f hS) d) := by
  have ha := towerCoefficientAdjoint_baseChange N hN A hA t D f hS d
  have h := sectionPullback_coefficient_naturality A f
    (affineTraceProjection S d) (affineTraceProjection T d) (affineTraceMap f d)
    z z' (affineTraceMap_isPullback f d).w hz h₀ h₁
    (affineLinearBaseCoefficient A N hA S d)
    (affineLinearBaseCoefficient A N hA T d)
    (dualizingComplex A (affineTraceProjection S d))
    (dualizingComplex A (affineTraceProjection T d))
    (vectorIntegrationBaseCoefficientPullback A N hA t f hS d).hom
    _ _ (dualizingComplexBaseChangeMap A (affineTraceMap_isPullback f d))
    (by simpa only [derivedSquareUpperStarIso, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, Category.assoc] using ha)
  simpa only [SectionComparisonArrows.sectionMap, Category.assoc, ordinaryFinitePullback,
    sectionInvariant, Iso.app_hom, Iso.app_inv] using h

end AlgebraicGeometry.Etale
