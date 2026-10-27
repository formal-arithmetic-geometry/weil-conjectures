module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Continuous coordinate partials and the real differential

Source: the agent coordinate-telescoping proof recorded in
`lem-sfb-continuous-partials-frechet-criterion`, using
Mathlib/Analysis/Calculus/MeanValue.lean,
`norm_image_sub_le_of_norm_deriv_le_segment_01'`.
Rudin, Principles of Mathematical Analysis, third edition, Theorem 9.21,
is a wanted reference, not a source read for this statement.
(blueprint: lem-sfb-continuous-partials-frechet-criterion)
-/

@[expose] public section

namespace Complex

/-- Continuous coordinate partial derivatives give a continuous real differential.
The functions `f` and `p j` are arbitrary extensions from the open set `U`.
Openness makes the derivatives along coordinate lines independent of these
extensions. `EuclideanSpace.single j 1` is the standard coordinate vector.
The final continuity assertion uses the operator norm on continuous real-linear maps.

Source: the agent coordinate-telescoping proof in the DAG node, based on
Mathlib/Analysis/Calculus/MeanValue.lean,
`norm_image_sub_le_of_norm_deriv_le_segment_01'`;
Rudin, third edition, Theorem 9.21 is wanted and has not been read.
(blueprint: lem-sfb-continuous-partials-frechet-criterion)

Proof plan:
1. Fix `x ∈ U`, set `a j = p j x`, and form the real-linear map
   `A h = ∑ j, h j • a j`. The bound `‖A h‖ ≤ (∑ j, ‖a j‖) * ‖h‖`
   proves its continuity. Given positive epsilon, choose a ball about `x`
   inside `U` on which all partials differ from `a j` by at most epsilon/m.
2. Join `x` to `x + h` by its successive coordinate segments. For sufficiently
   small `h`, every segment stays in that ball, by the Euclidean norm formula.
   Along segment `j`, subtract its linear contribution `t * h j • a j`.
   The one-variable chain rule gives derivative
   `h j • (p j (point on segment) - a j)`, including the constant case `h j = 0`.
   Apply lem-sfb-unit-interval-derivative-bound to bound this segment's
   remainder by `|h j| * epsilon/m`. No continuity of `f` is assumed here.
3. Telescope the segment increments. Since `∑ j, |h j| ≤ m * ‖h‖`,
   the total remainder is at most `epsilon * ‖h‖`. This proves real Frechet
   differentiability with differential `A`. Taking epsilon equal to one
   also bounds `‖f (x + h) - f x‖` by a constant times `‖h‖`, proving continuity.
4. For `x,y ∈ U`, the formula bounds the operator norm of `Df y - Df x`
   by `∑ j, ‖p j y - p j x‖`. Continuity of each partial makes this finite
   sum tend to zero at `x`, proving continuity of the differential.
-/
theorem continuous_partials_frechet_criterion
    (m : ℕ) (hm : 1 ≤ m)
    (U : Set (EuclideanSpace ℝ (Fin m))) (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin m) → ℂ)
    (p : Fin m → EuclideanSpace ℝ (Fin m) → ℂ)
    (hp : ∀ (j : Fin m) (x : EuclideanSpace ℝ (Fin m)), x ∈ U →
      HasDerivAt (fun t : ℝ ↦ f (x + t • EuclideanSpace.single j 1)) (p j x) 0)
    (hcp : ∀ j : Fin m, ContinuousOn (p j) U) :
    ContinuousOn f U ∧ DifferentiableOn ℝ f U ∧
      (∀ (x : EuclideanSpace ℝ (Fin m)), x ∈ U →
        ∀ h : EuclideanSpace ℝ (Fin m), fderiv ℝ f x h = ∑ j : Fin m, h j • p j x) ∧
      ContinuousOn (fderiv ℝ f) U := by
  sorry

end Complex
