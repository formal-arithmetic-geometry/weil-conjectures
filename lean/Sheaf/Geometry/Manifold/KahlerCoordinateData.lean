module

public import Sheaf.Geometry.Manifold.HermitianDolbeaultData

/-!
# Coordinate calculus for a Kähler metric

Source: Kong, Notes on Complex Geometry, §2.1 and §3.3, Definition 3.18, printed p.7
(blueprint: def-sfb-kahler-coordinate-data).

The existing Hermitian metric is used with its arguments reversed to obtain the convention
linear in the first argument. The fundamental form is evaluated on real tangent vectors.
Closedness is the cyclic coordinate formula for its exterior derivative. Wirtinger operators
are real directional derivatives, so they also apply to nonholomorphic metric coefficients.
-/

@[expose] public section

noncomputable section

universe u

open scoped Manifold ContDiff

namespace ComplexManifold

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]

/-- The first-linear Hermitian pairing in a coordinate chart, by tangent pullback.
Source: Kong §3.3, Definition 3.18 (blueprint: def-sfb-kahler-coordinate-data). -/
def chartHermitianPair (h : HermitianMetric n M)
    (e : OpenPartialHomeomorph M (Model n)) (z v w : Model n) : ℂ :=
  metricPair h.matrix (e.symm z) (chartTangent e z w) (chartTangent e z v)

/-- The coefficient `h_{j bar k} = h(∂x_j, ∂x_k)` in the first-linear convention.
Source: Kong §3.3, Definition 3.18 (blueprint: def-sfb-kahler-coordinate-data). -/
def chartHermitianCoefficient (h : HermitianMetric n M)
    (e : OpenPartialHomeomorph M (Model n)) (j k : Fin n) (z : Model n) : ℂ :=
  chartHermitianPair h e z (realCoordinateVector (j, false)) (realCoordinateVector (k, false))

/-- Evaluation of the real fundamental two-form `ω(v,w) = Re h(Jv,w)`, where `Jv = i v`.
Source: Kong §3.3, Definition 3.18 (blueprint: def-sfb-kahler-coordinate-data). -/
def chartFundamentalForm (h : HermitianMetric n M)
    (e : OpenPartialHomeomorph M (Model n)) (z v w : Model n) : ℝ :=
  (chartHermitianPair h e z (Complex.I • v) w).re

/-- The fundamental form is closed: its exterior derivative on three constant real
coordinate vector fields vanishes. All compatible holomorphic charts are tested.
The cyclic sum is `u ω(v,w) + v ω(w,u) + w ω(u,v)`, the coordinate definition of `dω`.
Source: Kong §3.3, Definition 3.18 (blueprint: def-sfb-kahler-coordinate-data). -/
def IsKahlerMetric (h : HermitianMetric n M) : Prop :=
  ∀ e ∈ IsManifold.maximalAtlas (𝓘(ℂ, Model n)) ∞ M, ∀ z ∈ e.target, ∀ u v w : Model n,
    fderivWithin ℝ (fun y ↦ chartFundamentalForm h e y v w) e.target z u +
      fderivWithin ℝ (fun y ↦ chartFundamentalForm h e y w u) e.target z v +
      fderivWithin ℝ (fun y ↦ chartFundamentalForm h e y u v) e.target z w = 0

/-- The Wirtinger derivative `∂z_l = (∂x_l - i ∂y_l)/2` of a smooth coefficient.
Source: Kong §2.1, Theorem 2.1 (blueprint: def-sfb-kahler-coordinate-data). -/
def wirtingerPartial (f : Model n → ℂ) (s : Set (Model n)) (l : Fin n)
    (z : Model n) : ℂ :=
  (fderivWithin ℝ f s z (realCoordinateVector (l, false)) -
    Complex.I * fderivWithin ℝ f s z (realCoordinateVector (l, true))) / 2

/-- The conjugate Wirtinger derivative `∂bar_z_l = (∂x_l + i ∂y_l)/2`.
Source: Kong §2.1, Theorem 2.1 (blueprint: def-sfb-kahler-coordinate-data). -/
def wirtingerBarPartial (f : Model n → ℂ) (s : Set (Model n)) (l : Fin n)
    (z : Model n) : ℂ :=
  (fderivWithin ℝ f s z (realCoordinateVector (l, false)) +
    Complex.I * fderivWithin ℝ f s z (realCoordinateVector (l, true))) / 2

end ComplexManifold
