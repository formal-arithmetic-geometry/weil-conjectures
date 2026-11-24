/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1ChartExchange
import WeilConjectures.AlgebraicGeometry.SfP1ProjectionTraceTransportFalse
import WeilConjectures.AlgebraicGeometry.SfP1ProjectionTraceTransportTrue

/-! # Transport of an ordinary exchange trace across a projective-line isomorphism

This comparison is natural in an arbitrary arrow out of the direct-image object.
It does not refer to a chart trace or a family of projective-line splittings.
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- Inverse exchange transports an arbitrary ordinary trace through an isomorphism
of projective lines. -/
theorem projectionTraceTransport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S)
    (a : Bool) :
    middleComparison A N hA t f i hi hS a ≫
        (ordinaryFinitePullback A i.hom).map (projectionExchange A N hA t S hS a) ≫
        (ordinaryFinitePullback A i.hom).map
          ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map τ ≫
            (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom) ≫
        (constantComparison A i).hom =
      coordinateTrace A N hA t f i hi hS τ a := by
  cases a
  · exact projectionTraceTransport_false A N hA t f i hi hS τ
  · exact projectionTraceTransport_true A N hA t f i hi hS τ

end AlgebraicGeometry.Etale.SfP1Transport
