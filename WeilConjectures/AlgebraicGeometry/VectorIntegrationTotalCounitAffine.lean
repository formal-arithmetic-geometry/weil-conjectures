/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationTotalCounitMaps

/-! # Flattening an affine tower preserves its ordered counit

Source: vector-bundle purity proof, paragraph 2, the ordered affine counit calculation.
(blueprint: lem-pur-vector-integration-total-counit-affine).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek upperStar lowerStar
  leftDerivedUpperStarComp Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

/-- The single affine trace on the flattened coordinate tower is the two-block
adjunction counit after the prescribed coefficient comparison. This statement has
no vector bundles, frames, opens, sum isomorphism, or chart exchange.
Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2, composition of the ordered affine adjunctions.
(blueprint: lem-pur-vector-integration-total-counit-affine).

Proof: first work with rank s+r, so the s base coordinates precede the r fibre
coordinates. Induct on r, expanding the single tower adjunction at its last line.
The recursive flattening is the affine-space functor applied to the previous
flattening. Exchange along that isomorphism commutes with the line counit by the
normalized projective-line base-change equation. Compose with the induction
hypothesis and use the composite-adjunction counit formula. The compact-support
comparisons agree because each is built from the same line compactification and
the normalized compact-support compositor, which satisfies associativity and units.
For the right-adjoint input, expand coefficientDescent and induct on r. Tensor
associativity and inverse-image composition identify its recursive descent with
the pullback of the ordered base tensor. The recursive purityPowerAdd comparison
and shifted-line pullback composition identify this with rightCoefficient.
Naturality moves that comparison across the left functors. The equality r+s=s+r
only reindexes the dimension of the ordered tensor. Cancel adjacent comparison
inverses to obtain the displayed equality. If r=0 or s=0, the same induction uses
the identity adjunction, inverse-image identity, tensor unitor and compositor unit.
No nonempty-base or positive-rank hypothesis is used. -/
theorem vectorIntegration_totalCounit_affine
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))) (r s : ℕ) :
    letI := affineTraceNoetherian T s
    (unboundedEtaleLowerShriekCompIso A
      (affineTraceProjection (affineTraceTower T s) r)
      (affineTraceProjection T s)).hom.app
      ((ordinaryFinitePullback A
        (affineTraceProjection (affineTraceTower T s) r ≫ affineTraceProjection T s)).obj
        (affineLinearBaseCoefficient A N hA T (r + s))) ≫
      VectorIntegrationTotalCounit.flattenedTrace N hN A hA t D T hT r s =
    VectorIntegrationTotalCounit.blockPrefix A N hA t T hT r s ≫
      (VectorIntegrationDirectSumCounit.blockAdjunction A N hA t D T hT r s).counit.app
        (ordinaryFiniteUnit A T) := by sorry

end AlgebraicGeometry.Etale
