/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralStratumChartRestrictionsData
import WeilConjectures.AlgebraicGeometry.IntegralStratumChartRestrictionsCharts
import WeilConjectures.AlgebraicGeometry.IntegralOperationsPreserveConstructible
import WeilConjectures.AlgebraicGeometry.IntegralStratumChartRestrictionsFunctorial

/-! # Exact integral stratum charts and their pullback square

Source: Bhatt--Scholze, Proposition 6.6.11, Lemmas 6.5.8--6.5.9 and
Remark 6.5.10 (blueprint: lem-a1-integral-stratum-chart-restrictions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace WeilConjectures.IntegralStratumCharts

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option linter.unusedVariables false in
/-- Exact integral restriction charts and their pullback square.
Source: Bhatt--Scholze, Proposition 6.6.11, Lemmas 6.5.8--6.5.9 and Remark 6.5.10
(blueprint: lem-a1-integral-stratum-chart-restrictions).

Proof assembly: chart existence and functoriality are separate strict substatements.
Constructibility follows directly from integralOperations_preserve_constructible; the
comparison witness comes from integralPullback_completedComparison. The two chart
substatements retain the following geometric and functorial argument.

Proof:
1. Integral-stratified-perfect-characterization identifies the recorded detailed category
with stratified perfect objects. On each stratum choose a pro-etale trivializing cover
and a bounded finite-projective representative. Its constant terms are flat, so
bounded-above-flat-kflat-site identifies ordinary scalar extension with derived extension.
Noetherian affine pieces have Noetherian underlying spaces; every open there is compact,
so the locally closed strata are constructible.
2. Proetale-immersion-limit-preservation and immersion-completed-pullback-comparison
provide exact ordinary stratum restriction, its coefficient identification and its
finite projections. Compose its inverse completion unit with the normalized gamma of
integral-pullback-completed-comparison.
3. Proetale-object-inverse-image-restriction identifies covering-object inverse image
with slice restriction. Site-restriction-module-adjunction-exact gives exactness and
limit preservation. Adic-stratum-completion-unit preserves completeness and finite
reductions without assuming the chart scheme Noetherian.
4. Slice-restriction-strict-derived-limit and roos-additive-comparison commute with
strict Roos models: each product projection intertwines the pulled-back transition;
apply that same product comparison in both cone coordinates. This fixes the maps
and all finite quotient projections, naturally in strict tower maps.
5. Local-derived-restriction-comparisons gives cohomology compatibility. Restricting
vanishing cohomology gives the identical interval for the scalar chart model.
6. Constructible-pullback-stratification gives the actual fibre-product strata, with
preimage images and disjointness. The same Noetherian argument makes them constructible.
Weakly-etale-composition-base-change and fpqc-covering-base-change give the pulled covers.
7. Integral-operations-preserve-constructible gives constructibility of the specified
pullback and of chart restrictions. Apply steps 2--4 on W for the primed restrictions.
8. Integral-pullback-composition along the two factorizations of the chart square gives
the natural comparison. Its finite normalization, together with the projection-preserving
restriction comparisons, gives exactly the reductions equation in PullbackSquare.
9. Integral-pullback-completed-comparison identifies the specified pullback with the
strict completed pullback. Completed-pullback-triangles transports shifts and triangles
through gamma, with the comparison's stated shift square. Finite inverse image, products,
1-s and both cone coordinates commute with constant scalar multiplication, giving
R-linearity. This is exactness on constructible objects, not global t-exactness.
-/
theorem integral_stratum_chart_restrictions {X W : Scheme.{u}} (h : W ⟶ X)
    [IsNoetherian X] [IsNoetherian W]
    (_hXdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hWdim : ∃ n : ℕ, topologicalKrullDim W ≤ n)
    (_hXl : IsUnit (l : Γ(X, ⊤))) (_hWl : IsUnit (l : Γ(W, ⊤))) :
    (∀ K : (constructible l E X).FullSubcategory, Nonempty (Charts l E h K.obj)) ∧
    (∀ K : (constructible l E X).FullSubcategory,
      sfIntegralConstructible l E W ((IntegralCompletedComparison.integral l E h).obj K.obj)) ∧
    ∃ c : IntegralCompletedComparison.Comparison l E h,
      (integralDerivedPullback l E h).Additive ∧
      (∀ (a : Padic.coefficientExtensionIntegers l E)
        (K L : (constructible l E X).FullSubcategory) (f : K ⟶ L),
        (integralDerivedPullback l E h).map
            ((integralScalarDerivedAction l E X a).app
              ((ImmersionCompletedPullback.transport l E X).obj K.obj) ≫
                (ImmersionCompletedPullback.transport l E X).map f.hom) =
          (integralScalarDerivedAction l E W a).app
              ((IntegralCompletedComparison.integral l E h).obj K.obj) ≫
            (IntegralCompletedComparison.integral l E h).map f.hom) ∧
      (fun [shift : (integralDerivedPullback l E h).CommShift ℤ] ↦
        ∀ T : Triangle (DerivedCategory (integralTowerModules l E X)),
          T ∈ distTriang _ →
          sfIntegralConstructible l E X T.obj₁ →
          sfIntegralConstructible l E X T.obj₂ →
          sfIntegralConstructible l E X T.obj₃ →
          (integralDerivedPullback l E h).mapTriangle.obj T ∈ distTriang _)
        (shift := c.derivedShift) := by
  classical
  have hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x) := by
    intro x
    simpa only [map_natCast] using
      RingHom.isUnit_map (X.presheaf.germ ⊤ x trivial).hom _hXl
  have hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w) := by
    intro w
    simpa only [map_natCast] using
      RingHom.isUnit_map (W.presheaf.germ ⊤ w trivial).hom _hWl
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (show IsUnit (l : X.residueField x) from by
      simpa only [map_natCast] using RingHom.isUnit_map (X.residue x).hom (hX x)).invertible
  let : ∀ w : W, Invertible (l : W.residueField w) := fun w ↦
    (show IsUnit (l : W.residueField w) from by
      simpa only [map_natCast] using RingHom.isUnit_map (W.residue w).hom (hW w)).invertible
  refine ⟨?_, ?_, ?_⟩
  · exact integral_stratum_charts l E h _hXdim _hWdim _hXl _hWl
  · intro K
    exact ((integralOperations_preserve_constructible l E h).1
      ((ImmersionCompletedPullback.transport l E X).obj K.obj) K.property).1
  · obtain ⟨c⟩ := IntegralCompletedComparison.integralPullback_completedComparison l E h hW hX
    exact ⟨c, integral_stratum_pullback_functorial l E h _hXdim _hWdim _hXl _hWl c⟩

end WeilConjectures.IntegralStratumCharts
