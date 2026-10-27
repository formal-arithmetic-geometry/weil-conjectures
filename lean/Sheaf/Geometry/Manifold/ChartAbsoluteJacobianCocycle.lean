module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Absolute chart Jacobians

Source: the agent-stated real test-density convention supporting Demailly, Part I §3.A–3.B,
printed pp.11–13 (the cited PDF is unavailable locally and was not independently verified).
(blueprint: lem-sfb-chart-absolute-jacobian-cocycle)

## Main definitions and statements

* `OpenPartialHomeomorph.chartAbsoluteJacobian` is the absolute determinant of the ordinary
  real derivative of a coordinate transition, evaluated at the first chart's coordinate.
* `OpenPartialHomeomorph.chartAbsoluteJacobian_cocycle` states smoothness, positivity,
  smoothness of the reciprocal, and the diagonal, inverse and triple-overlap identities.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open scoped ContDiff

namespace OpenPartialHomeomorph

/-- The absolute chart-transition Jacobian, using the standard coordinates of `ℝ^m`.
The entry in row `a`, column `b` is the `a`-coordinate of the derivative applied to the
`b`-th standard basis vector. Only values on `x.source ∩ y.source` are used. When `m = 0`,
`Matrix.det` is the empty determinant `1`.

Source: the agent-stated real test-density convention supporting Demailly, Part I §3.A–3.B,
printed pp.11–13, not independently verified locally.
(blueprint: lem-sfb-chart-absolute-jacobian-cocycle) -/
noncomputable def chartAbsoluteJacobian {m : ℕ} {N : Type u} [TopologicalSpace N]
    (x y : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m))) (p : N) : ℝ :=
  |Matrix.det (fun a b : Fin m ↦
    (fderiv ℝ (fun q ↦ y (x.symm q)) (x p) (EuclideanSpace.single b 1)) a)|

/-- Absolute chart Jacobians are a positive smooth cocycle for all compatible smooth charts.
Maximal-atlas membership includes every chart compatible with the given atlas, not just its
chosen members. The self model has no boundary, and no separation, countability, orientation
or compactness assumption is imposed.

Source: the agent-stated real test-density convention supporting Demailly, Part I §3.A–3.B,
printed pp.11–13, not independently verified locally.
(blueprint: lem-sfb-chart-absolute-jacobian-cocycle)

Proof plan:
1. In dimension zero the determinant is `1` by `Matrix.det_isEmpty`, so all assertions reduce
   to smoothness of constants and `1 = 1`. Empty overlaps impose no conditions.
2. The chart-transition domains are open. Compatibility with the atlas makes transitions
   smooth: near any point factor through an atlas chart. By
   `lem-sfb-real-smooth-differentiation`, the ordinary derivative is smooth there.
3. Differentiate the inverse-chart identities by the chain rule. The two derivative
   matrices multiply to the identity. Determinant multiplicativity from
   `lem-sfb-matrix-cramer-determinant-identities` makes both determinants nonzero and gives
   the inverse identity after absolute values. The identity chart transition gives the
   diagonal identity.
4. Each derivative matrix entry is smooth, hence its determinant is smooth by the finite
   Leibniz formula in `def-weil-pbc-matrix-determinant`. Near a point with nonzero determinant,
   continuity makes its sign constant, so its absolute value is locally the determinant or
   its negative. Composition with any compatible chart gives manifold smoothness.
5. The reversed pair is smooth by step 4; the inverse identity of step 3 identifies it with
   the reciprocal, which is therefore smooth without a separate inversion theorem.
6. On a triple overlap cancel the middle chart and differentiate the resulting composition.
   Determinant multiplicativity and `abs_mul` give the displayed cocycle identity. All
   arguments take place on open Euclidean neighbourhoods and require no global topology.
-/
theorem chartAbsoluteJacobian_cocycle {m : ℕ} {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m))) ∞ N]
    (x y : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)))
    (hx : x ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m))) ∞ N)
    (hy : y ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m))) ∞ N) :
    ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m)))
      (modelWithCornersSelf ℝ ℝ) ∞ (x.chartAbsoluteJacobian y) (x.source ∩ y.source) ∧
    (∀ p ∈ x.source ∩ y.source, 0 < x.chartAbsoluteJacobian y p) ∧
    ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m)))
      (modelWithCornersSelf ℝ ℝ) ∞ (fun p ↦ (x.chartAbsoluteJacobian y p)⁻¹)
      (x.source ∩ y.source) ∧
    (∀ p ∈ x.source, x.chartAbsoluteJacobian x p = 1) ∧
    (∀ p ∈ x.source ∩ y.source,
      y.chartAbsoluteJacobian x p * x.chartAbsoluteJacobian y p = 1) ∧
    (∀ z : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)),
      z ∈ IsManifold.maximalAtlas
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m))) ∞ N →
      ∀ p ∈ x.source ∩ y.source ∩ z.source,
        x.chartAbsoluteJacobian z p =
          y.chartAbsoluteJacobian z p * x.chartAbsoluteJacobian y p) := by
  sorry

end OpenPartialHomeomorph
