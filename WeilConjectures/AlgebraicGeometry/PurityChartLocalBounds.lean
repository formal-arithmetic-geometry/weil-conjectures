/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.PurityAffineChartCover
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntrinsicConstructibleIntervals
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations

/-! # Exceptional bounds on one chosen affine chart

Source: blueprint `thm-pur-general-admissibility.proof.md`, Steps 1--3.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/-- The smooth-then-closed computation on a single chart, before taking maxima or
performing descent. The constructible clause has no finite-Tor assumption.
Source: blueprint `thm-pur-general-admissibility.proof.md`, Steps 1--3
(blueprint: lem-pur-chart-local-bounds).

Proof: restrict the input to the affine base open; exact open inverse image preserves
constructible intervals and Tor intervals. Give a bounded constructible input its
bounded-below etale witness. The witnessed base-open and affine-chart comparisons identify
restriction of the exceptional image with the closed exceptional image of the exceptional
image under the affine-space projection. The projection is separated and smooth of pure
relative dimension d. Smooth exceptional preservation gives the interval [a-2d,b-2d]
for each of the independent cohomological and Tor inputs, retaining bounded
constructibility. Closed etale transport bounds, using the stipulated complement
condition, give [a-2d,b-2d+c+1]. Transfer these predicates along the chart comparison.
This is a local assertion for one chart; no cover descent or uniform maximum is used. -/
theorem chart_local_bounds (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (C : Scheme.PurityAffineChartCover f)
    (v : Fin C.baseCount) (i : Fin (C.chartCount v)) (c : ℕ)
    (hc : @Scheme.HasOpenComplementCondition P.Coefficient _ _ _ _
      (C.complement v i).ι inferInstance (C.complement_quasiCompact v i) c)
    (a b : ℤ) (hab : a ≤ b) :
    (∀ K, constructibleInterval P.coefficients.l P.extension P.level P.level_pos Y a b K →
      constructibleInterval P.coefficients.l P.extension P.level P.level_pos
        (C.chartOpen v i).toScheme
        (a - 2 * (C.embeddingDimension v i : ℤ))
        (b - 2 * (C.embeddingDimension v i : ℤ) + (c : ℤ) + 1)
        ((proEtaleConstantRingDerivedPullback P.Ring (C.chartOpen v i).ι).obj
          ((P.exceptionalInverseImage f).obj K))) ∧
    (∀ K, finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K →
      Scheme.HasProEtaleTorAmplitude Y P.Ring K a b →
      Scheme.HasProEtaleTorAmplitude (C.chartOpen v i).toScheme P.Ring
        ((proEtaleConstantRingDerivedPullback P.Ring (C.chartOpen v i).ι).obj
          ((P.exceptionalInverseImage f).obj K))
        (a - 2 * (C.embeddingDimension v i : ℤ))
        (b - 2 * (C.embeddingDimension v i : ℤ) + (c : ℤ) + 1)) := by sorry

end WeilConjectures.PurityFiniteSetting
