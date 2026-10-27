/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationABase

/-! # Naturality of the integral pullback Hom comparison

Source: Stacks Project, Tag 0GMX; blueprint main-20261015
prop-pod-dual-tate-data-compatibility, Steps 8--11
(blueprint: stage3-derived-automorphism-continuation-a-integral-naturality).

The naturality field of `podIntegralHomComparison_laws`, left as a statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Naturality component of the integral pullback Hom compatibility.
Source: Stacks 0GMX; node lem-pod-derived-automorphism-hom-evaluation, steps 8--11.
Proof: both sides are maps into `H_X(FQ)`; compare their inverse transposes. The
transposition of `podIntegralClosed` is the completion-unit precomposition
followed by the ordinary tensor-Hom adjunction
(lem-pod-reindexing-completed-evaluation-reflection), hence natural in the
permitted pair as well as in the parameter, so evaluation is dinatural:
`T(H(a,b),1) ≫ ev_Q = T(1,a) ≫ ev_P ≫ b` for `(a,b) : P ⟶ Q`. With the
naturality of `μ` (lem-pur-derived-pullback-tensor-iso) the inverse transpose of
the left side becomes `T(1,Fa) ≫ μ⁻¹ ≫ F(ev_P) ≫ F b`. The right side gives
`T(1,Fa) ≫ T(c_P,1) ≫ ev ≫ F b` by the same dinaturality on `X`, and
`T(c_P,1) ≫ ev = μ⁻¹ ≫ F(ev_P)` is the evaluation equation. The transposes
agree, so the maps agree.
(blueprint: stage3-derived-automorphism-continuation-a-integral-naturality). -/
theorem podIntegralHomComparison_naturality :
    ∀ (P Q : (constructibleIntegralHomPairs l E Y).FullSubcategory) (f : P ⟶ Q),
      (constructibleIntegralPullback l E g).map
          ((constructibleIntegralHom l E Y).map f) ≫
        podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
        (canonicalIntegralPullbackTensor l E g) Q =
      podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
        (canonicalIntegralPullbackTensor l E g) P ≫
        (constructibleIntegralHom l E X).map
          ((podPairPullback (constructibleIntegralPullback l E g)
            (constructibleIntegralHomPairs l E Y) (constructibleIntegralHomPairs l E X)
            (podIntegralPairs_pullback l E g)).map f) := by
  sorry

end WeilConjectures
