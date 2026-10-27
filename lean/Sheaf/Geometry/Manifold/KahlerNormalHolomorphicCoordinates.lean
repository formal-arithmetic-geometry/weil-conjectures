module

public import Sheaf.Geometry.Manifold.KahlerCoordinateData
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Normal holomorphic coordinates for a Kähler metric

Source: Kong, Notes on Complex Geometry, §3.3, Definition 3.18 and Theorem 3.19, printed p.7
(blueprint: lem-sfb-kahler-normal-holomorphic-coordinates).

The metric coefficients use Kong's first-linear convention. Both Wirtinger first derivatives
vanish, and the fundamental-form identity holds on the entire coordinate neighborhood.
-/

@[expose] public section

universe u

open scoped Manifold ContDiff

namespace ComplexManifold

/-- A Kähler metric admits a centered holomorphic chart with identity metric matrix and
vanishing holomorphic and antiholomorphic first derivatives at the center.
Source: Kong §3.3, Definition 3.18 and Theorem 3.19, printed p.7
(blueprint: lem-sfb-kahler-normal-holomorphic-coordinates).

Proof plan (the four steps of the DAG):
1. Start with a holomorphic chart centered at `a`. Use an orthonormal complex basis of the
   tangent metric, with arguments reversed for Mathlib's convention, and change coordinates
   by the inverse basis matrix. The metric coefficient matrix is now the identity at zero.
   This uses lem-sfb-finite-complex-orthonormal-basis.
2. Expanding `Re h(Jv,w) = -Im h(v,w)` gives the displayed fundamental-form identity.
   Closedness implies `∂_l h_{j bar k} = ∂_j h_{l bar k}`. Thus the constants
   `C^k_{jl} = ∂_l h_{j bar k}(0)` are symmetric in `j,l`.
3. The holomorphic polynomial `F^k(z) = z_k - (1/2) Σ C^k_{jl} z_j z_l` has derivative the
   identity at zero and second derivatives `-C^k_{jl}`. Apply the four clauses of
   lem-sfb-complex-analytic-inverse-toolkit. Restrict the analytic local inverse to an open
   neighborhood inside the old chart image, giving the new coordinate `z = F⁻¹ ∘ u`.
4. Transform the metric by `h'_{a bar b}(z) = Σ h_{p bar q}(F(z)) ∂_a F^p conj(∂_b F^q)`.
   Its value at zero is the identity. Differentiation gives `C^b_{ac} - C^b_{ac} = 0`.
   Hermitian symmetry gives the barred derivatives as conjugates of the unbarred ones.
   The form identity from step 2 holds throughout the final chart. -/
theorem exists_kahler_normal_holomorphic_coordinates
    (n : ℕ) (hn : 1 ≤ n) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (Model n) M] [IsManifold (𝓘(ℂ, Model n)) ∞ M]
    (h : HermitianMetric n M) (hclosed : IsKahlerMetric h) (a : M) :
    ∃ e : OpenPartialHomeomorph M (Model n),
      e ∈ IsManifold.maximalAtlas (𝓘(ℂ, Model n)) ∞ M ∧ a ∈ e.source ∧ e a = 0 ∧
      (∀ z ∈ e.target, ∀ v w : Model n,
        (chartFundamentalForm h e z v w : ℂ) =
          Complex.I / 2 * ∑ j : Fin n, ∑ k : Fin n,
            chartHermitianCoefficient h e j k z *
              (v j * star (w k) - w j * star (v k))) ∧
      (∀ j k : Fin n, chartHermitianCoefficient h e j k 0 = if j = k then 1 else 0) ∧
      ∀ j k l : Fin n,
        wirtingerPartial (chartHermitianCoefficient h e j k) e.target l 0 = 0 ∧
        wirtingerBarPartial (chartHermitianCoefficient h e j k) e.target l 0 = 0 := by
  sorry

end ComplexManifold
