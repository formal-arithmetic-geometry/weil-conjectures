/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts

/-! # Rank-zero chart coefficient normalization

Source: blueprint vector-bundle purity, paragraph 2, prescribed counit on a frame.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The rank-zero chart coefficient becomes the constant-unit pullback map after the
chart/projection pullback compositor.
Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2, the prescribed local affine counit.
(blueprint: lem-pur-vector-integration-chart-coefficient-zero).

Proof: expand the zero cases of vectorIntegrationBaseCoefficientPullback and
affineLinearCoefficientDescent. The first is ordinaryFiniteUnitPullback; the second
is the inverse of affineLinearPullbackId at the unit. Write a for the chart and p for
the bundle projection. The chart square gives a≫p = id≫V.ι. The equality transport
between the two pullback compositors therefore identifies their composite with the
inverse compositor for a≫p=V.ι followed by the compositor for id≫V.ι=V.ι.
Cancel the first against the displayed leading compositor. Naturality moves the
unit pullback through the identity-pullback comparison. The latter is the canonical
leftDerivedUpperStarId (expand the definitions of their exact/derived comparisons).
The left unit law for leftDerivedUpperStarComp then cancels the remaining compositor
and identity comparison. The map left is exactly ordinaryFiniteUnitPullback.
No nonempty-open or nonzero-ring assumption is used. -/
theorem vectorIntegration_chartCoefficient_zero
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank 0]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S 0 F V)
    (hc : vectorIntegrationChart S 0 F V e ≫ VectorBundleZeroSection.π S 0 F = V.ι) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (vectorIntegrationChart S 0 F V e) (VectorBundleZeroSection.π S 0 F)
        V.ι hc.symm).hom.app (ordinaryFiniteUnit A S) ≫
      (vectorIntegrationChartCoefficient A N hA t S hS 0 F V e).hom =
        (ordinaryFiniteUnitPullback A V.ι).hom := by sorry

end AlgebraicGeometry.Etale
