/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineTraceSupplement

/-! # Unbounded scalar compatibility of the normalized projective-line counit

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
  sk-lem-sp-reduction-exceptional.proof.md, Charts.
(blueprint: lem-pur-ordinary-chart-p1-counit-scalar)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/--
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
  sk-lem-sp-reduction-exceptional.proof.md, Charts.
(blueprint: lem-pur-ordinary-chart-p1-counit-scalar)

The statement is the normalized scalar compatibility of the actual ordinary finite
projective-line counits.  It uses the canonical projective-line datum, whose counit is
specified by the inverse proper projection and the normalized trace.  The proof is the
three-step chart argument: vector-trace scalar descent, the unbounded proper projection
square, and the strong-monoidal unit equation.
-/
theorem ordinaryChartP1CounitScalarStatement
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (K : DerivedCategoryModule A S) :
    (scalarMate φ (ProjectiveLine S ↘ S)).app
        ((ordinaryFiniteP1Right A N hA S).obj K) ≫
      (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
        (ProEtale.reductionEtaleP1ScalarIso φ S N hA hB hS K).hom ≫
      (projectiveLineTraceDatum N hN B hB S hS).adjunction.counit.app
        ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map
      ((projectiveLineTraceDatum N hN A hA S hS).adjunction.counit.app K) := by
  sorry

end AlgebraicGeometry.Etale
