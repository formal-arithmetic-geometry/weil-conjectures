/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1ChartExchange
import WeilConjectures.AlgebraicGeometry.SfP1ProjectionTraceFalseTail

/-! # False projection case of projective-line trace transport

This is the fixed-`false` component of the arbitrary-trace transport equation.
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/--
The ordinary inverse-exchange trace transport for the first projection: the `false`
component of the trace transport equation, for an arbitrary arrow `τ`.
-/
theorem projectionTraceTransport_false
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S) :
    middleComparison A N hA t f i hi hS false ≫
        (ordinaryFinitePullback A i.hom).map (projectionExchange A N hA t S hS false) ≫
        (ordinaryFinitePullback A i.hom).map
          ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map τ ≫
            (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom) ≫
        (constantComparison A i).hom =
      coordinateTrace A N hA t f i hi hS τ false := by
  calc
    middleComparison A N hA t f i hi hS false ≫
        (ordinaryFinitePullback A i.hom).map
          (projectionExchange A N hA t S hS false) ≫
        (ordinaryFinitePullback A i.hom).map
          ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map τ ≫
            (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom) ≫
        (constantComparison A i).hom =
      middleComparison A N hA t f i hi hS false ≫
        (ordinaryFinitePullback A i.hom).map
          (projectionExchange A N hA t S hS false) ≫
        (ordinaryFinitePullback A i.hom).map
          (falseProjectionChartFactor A N hA t S hS ≫
            falseProjectionChartFactorInv A N hA t S hS) ≫
        (ordinaryFinitePullback A i.hom).map
          ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map τ ≫
            (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom) ≫
        (constantComparison A i).hom := by
          have hc := falseProjectionChartFactor_cancel A N hA t S hS
          have hc' := congrArg (fun z ↦
            middleComparison A N hA t f i hi hS false ≫
              (ordinaryFinitePullback A i.hom).map
                (projectionExchange A N hA t S hS false) ≫
              (ordinaryFinitePullback A i.hom).map z ≫
              (ordinaryFinitePullback A i.hom).map
                ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map τ ≫
                  (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom) ≫
              (constantComparison A i).hom) hc
          simpa using hc'.symm
    _ = middleComparison A N hA t f i hi hS false ≫
        (ordinaryFinitePullback A i.hom).map
          (ordinaryFiniteP1DiagonalChartMap A N hA t S hS false) ≫
        (ordinaryFinitePullback A i.hom).map
          (falseProjectionChartFactorInv A N hA t S hS) ≫
        (ordinaryFinitePullback A i.hom).map
          ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map τ ≫
            (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom) ≫
        (constantComparison A i).hom := by
          have h := falseProjectionChartPasting A N hA t f i hi hS
          have h' := congrArg (fun z ↦ z ≫
            (ordinaryFinitePullback A i.hom).map
              (falseProjectionChartFactorInv A N hA t S hS) ≫
            (ordinaryFinitePullback A i.hom).map
              ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map τ ≫
                (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom) ≫
            (constantComparison A i).hom) h
          simpa only [falseProjectionChartFactor, Functor.map_comp,
            Category.assoc] using h'
    _ = coordinateTrace A N hA t f i hi hS τ false :=
      falseProjectionChartTail A N hA t f i hi hS τ

end AlgebraicGeometry.Etale.SfP1Transport
