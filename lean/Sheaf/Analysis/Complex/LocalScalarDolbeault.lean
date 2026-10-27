module

public import Sheaf.Analysis.Complex.ScalarDolbeaultForms
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Sheaf.Analysis.Complex.CutoffCauchyTransform

/-! # The local scalar Dolbeault lemma

Source: Demailly, Complex Analytic and Differential Geometry, I §3.C, (3.14) and the
Cauchy--Riemann criterion, and I §3.E, Lemma (3.29), with `p = 0`.
(blueprint: lem-sfb-local-scalar-dolbeault)
-/

@[expose] public section

namespace ComplexManifold

/-- Every closed smooth scalar form of positive antiholomorphic degree has a smooth
primitive on a neighborhood of any prescribed point. Degree `q+1` covers all positive
degrees, including degrees above the dimension.
Source: Demailly I §3.E, Lemma (3.29), and I §8, Exercise 8.5.
(blueprint: lem-sfb-local-scalar-dolbeault)

Proof: First obtain `∂bar² = 0` as the component of antiholomorphic degree two in
`d² = 0`, using lem-sfb-chart-exterior-derivative-square-zero, after substituting
`dx = (dz + dbar z)/2` and `dy = (dz - dbar z)/(2i)`. Independence of the wedge basis
identifies that component. If the degree exceeds `n`, the form vanishes and the zero
primitive on `U` suffices; this includes every positive degree when `n = 0`.
Otherwise choose nested polydiscs centered at `a` inside `U`, with radii `r_j < R_j`.
Descend through coordinates `k = n,...,1`: the current closed form uses only indices
at most `k`. Write it as `dbar z_k ∧ f + g` with both remaining wedge parts using
indices below `k`. Closedness implies that all coefficients of `f` and `g` have zero
conjugate derivatives in coordinates above `k`, by inspecting each corresponding
wedge coefficient. Apply lem-sfb-cauchy-transform-parameters in coordinate `k`, with
all other coordinates real parameters, to each coefficient of `f`. The resulting
form `b_k` is smooth, its derivative in coordinate `k` is `f`, and its conjugate
parameter derivatives above `k` vanish by the commutation and linearity formulas.
Subtract `∂bar b_k` on the smaller polydisc. This removes exactly the terms involving
index `k`, introduces no larger indices, and preserves closedness by `∂bar² = 0`.
After the last step a positive-degree form with no available indices is zero.
Restrict the finitely many `b_k` to the smallest polydisc and add them. Telescoping
gives the requested primitive, smooth on this open neighborhood of `a` inside `U`.
-/
theorem local_scalar_dolbeault (n q : ℕ) (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (a : Fin n → ℂ) (ha : a ∈ U) (α : ScalarAntiholomorphicForm n (q + 1) U)
    (hα : IsSmoothScalarForm α) (hclosed : scalarDolbeault α = 0) :
    ∃ (V : Set (Fin n → ℂ)) (_hV : IsOpen V) (hVU : V ⊆ U),
      a ∈ V ∧ ∃ β : ScalarAntiholomorphicForm n q V,
        IsSmoothScalarForm β ∧ scalarDolbeault β = restrictScalarForm hVU α := by
  sorry

/-- The degree-zero kernel of `∂bar` consists exactly of holomorphic functions.
There is a unique increasing tuple of length zero, so the universal quantifier on
`J` refers to the single coefficient of a function. Complex differentiability on
an open domain is holomorphicity; the zero extension is irrelevant off that domain.
Source: Demailly I §3.C, (3.14) and the Cauchy--Riemann criterion, printed pp.23--24.
(blueprint: lem-sfb-local-scalar-dolbeault)

Proof: Fix `x ∈ U` and the real derivative `A` of its smooth coefficient. Vanishing
of the coordinate conjugate derivatives says `A(e_j) + i A(i e_j) = 0`, equivalently
`A(i e_j) = i A(e_j)`. Expanding any vector in the real basis `e_j, i e_j` shows this
is equivalent to `A(i v) = i A(v)` for every `v`, hence to complex linearity of `A`.
Its continuity is already part of the real Frechet derivative. Apply
lem-sfb-real-derivative-complex-linear, namely `differentiableAt_iff_restrictScalars`
for `ℝ ⊆ ℂ`, to obtain complex differentiability exactly when these equations hold.
The domain is open, so its within-derivatives are the derivatives of the interior
germs. Doing this at every point proves the equivalence. Empty domains and `n = 0`
are included, with no derivative coordinates in the latter case.
-/
theorem scalar_dolbeault_zero_iff_holomorphic (n : ℕ) (U : Set (Fin n → ℂ))
    (hU : IsOpen U) (α : ScalarAntiholomorphicForm n 0 U) (hα : IsSmoothScalarForm α) :
    scalarDolbeault α = 0 ↔
      ∀ J : Fin 0 ↪o Fin n, DifferentiableOn ℂ (scalarCoefficientExtension U (α J)) U := by
  sorry

end ComplexManifold
