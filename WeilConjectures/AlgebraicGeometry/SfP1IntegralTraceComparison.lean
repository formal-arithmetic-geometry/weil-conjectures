/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
import WeilConjectures.AlgebraicGeometry.SfP1ProjectionTraceTransport

/-! # Transport of the two projection traces

This equation concerns a fixed explicit trace and needs no diagonal Ext class.
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- The base-change equation for the splitting trace identifies the two chart
traces with the coordinate traces of the explicitly transported trace. -/
theorem traceComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange A N hA t d)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    middleComparison A N hA t f i hi hS a ≫
        (ordinaryFinitePullback A i.hom).map
          (arbitraryBaseFiniteP1DiagonalTrace A N hA t d S hS a) ≫
        (constantComparison A i).hom =
      coordinateTrace A N hA t f i hi hS (d S hS).trace a := by
  have htrace := (hbc (ProjectiveLine S ↘ S) hS
    (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).2
  have hchart : arbitraryBaseFiniteP1DiagonalTrace A N hA t d S hS a =
      projectionExchange A N hA t S hS a ≫
        ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map (d S hS).trace ≫
          (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom) := by
    rw [arbitraryBaseFiniteP1DiagonalTrace, ← chartExchange A N hA t S hS a]
    simpa only [Category.assoc] using
      congrArg (fun z ↦ projectionExchange A N hA t S hS a ≫ z) htrace.symm
  rw [hchart, Functor.map_comp]
  simpa only [Category.assoc] using
    projectionTraceTransport A N hA t f i hi hS (d S hS).trace a

end AlgebraicGeometry.Etale.SfP1Transport
