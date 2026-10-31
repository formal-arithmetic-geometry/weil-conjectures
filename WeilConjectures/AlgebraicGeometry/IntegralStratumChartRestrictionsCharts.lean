/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralStratumChartRestrictionsData

/-! # Auxiliary steps for integral stratum restrictions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace WeilConjectures.IntegralStratumCharts

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The geometric and exact-restriction part of the integral chart argument.
Source: Bhatt--Scholze, Proposition 6.6.11, Lemmas 6.5.8--6.5.9 and Remark 6.5.10
(blueprint: lem-a1-integral-stratum-charts-existence).

Proof: Use the detailed integral category comparison and the stratified-perfect
characterization to choose finite locally closed strata and pro-etale perfect charts.
Every locally closed subset of a Noetherian space is constructible. Choose bounded
finite-projective representatives of the perfect values. Exact restriction along
stratum immersions preserves limits and identifies coefficients, by the immersion
comparison; restriction along covering objects is slice restriction, hence exact and
limit preserving. Its product comparison commutes with the transition endomorphism
of a strict tower; the same comparison in both cone coordinates gives the unique
Roos comparison and preserves the derived-limit projections. The completion unit
and gamma identify these restrictions with integral pullback, naturally and with
all finite projections. Cohomology commutes with exact restriction, so the scalar
models inherit every cohomological interval of the input. Base change the strata
and the pro-etale covering families to W; weak etaleness and covering are preserved.
Repeat the restriction construction on W. Compose the normalized integral pullback
composition maps for the two factorizations of each cartesian chart square.
Their finite normalization and the projection equations give precisely the
PullbackSquare.reductions equation. This supplies all fields of Charts, including
primed restriction and comparison fields. Empty strata and schemes need no choices
of points, and no Noetherian hypothesis is made on covering objects. -/
theorem integral_stratum_charts {X W : Scheme.{u}} (h : W ⟶ X)
    [IsNoetherian X] [IsNoetherian W]
    (_hXdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hWdim : ∃ n : ℕ, topologicalKrullDim W ≤ n)
    (_hXl : IsUnit (l : Γ(X, ⊤))) (_hWl : IsUnit (l : Γ(W, ⊤))) :
    (∀ K : (constructible l E X).FullSubcategory, Nonempty (Charts l E h K.obj)) := by sorry

end WeilConjectures.IntegralStratumCharts
