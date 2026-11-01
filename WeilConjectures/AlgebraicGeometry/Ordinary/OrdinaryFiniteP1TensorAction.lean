/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineTensorActions.OrdinaryAffineTensorActions
import WeilConjectures.CategoryTheory.Normalized.NormalizedTensorCounitAction
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.LeftCoefficientProjectionAction
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.Compactification.ProjectiveSpace

/-! # Coefficient linearity of the normalized ordinary projective-line counit -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale


/-- A normalized projective-line counit respects the ordered tensor action.
Source: blueprint affine-space top trace, the projective factor in step 3;
Stacks Tags 0B56 and 0GL1
(blueprint: lem-pur-ordinary-finite-p1-tensor-action).

Proof: the finite-coefficient proper projection theorem makes every ordered
projection invertible. Replace the constant single complex in normalization by
the derived monoidal unit using its canonical isomorphism. The associativity of
the actual ordered proper projection and normalizedTensorCounit_action give the
stated action identity. The tensorator is precisely the inverse of
ordinaryFiniteTensorPullback, so no choice of comparison or trace occurs. -/
theorem ordinaryFiniteP1Counit_tensorAction
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (D : OrdinaryFiniteP1Datum A N hA t S hS)
    (H K : DerivedCategoryModule A S) :
    (OrdinaryAffineTensorActions.properActionNat A S H).app
        ((ordinaryFiniteP1Right A N hA S).obj K) ≫
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
        (OrdinaryAffineTensorActions.properStrength A N hA S H K).hom ≫
      D.adjunction.counit.app (((ordinaryFiniteTensor A S).obj H).obj K) =
        ((ordinaryFiniteTensor A S).obj H).map (D.adjunction.counit.app K) := by
  sorry

end AlgebraicGeometry.Etale
