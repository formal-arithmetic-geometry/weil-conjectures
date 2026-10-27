module

public import Sheaf.Geometry.Manifold.KahlerCoordinateData
public import Sheaf.Geometry.Manifold.FormalDolbeaultOperators

/-!
# Kähler comparison of the de Rham and Dolbeault Laplacians

Source: Kong, Notes on Complex Geometry, §6.4, Proposition 6.12, printed p.26
(blueprint: lem-sfb-kahler-laplacian-identity).

This is an equality of operators on all smooth complex forms. Formal adjoints are
characterized by compactly supported tests; no compactness or L² condition is imposed.
-/

@[expose] public section

universe u

open scoped Manifold ContDiff

namespace ComplexManifold

/-- The de Rham Laplacian is twice the Dolbeault Laplacian on a Kähler manifold.
Both sides are expanded as `D D* + D* D`, with `d = bar∂ + ∂`.
Source: Kong, Notes on Complex Geometry, §6.4, Proposition 6.12, printed p.26
(blueprint: lem-sfb-kahler-laplacian-identity).

Proof plan, following the five DAG steps:
1. Put A = ∂ and B = bar∂. The type differential relations of
   lem-sfb-dolbeault-acyclic-resolution give A² = B² = AB + BA = 0 locally in
   holomorphic charts, hence globally. Compact-test integration by parts gives
   d* = A* + B*. For uniqueness, pair the difference applied to an arbitrary smooth
   form with a nonnegative chart cutoff times that difference. Positivity forces
   it to vanish on the chart, so the identity holds on all smooth forms.
2. By lem-sfb-kahler-first-order-commutators, for Q = Λ and the same metric,
   [Q,A] = i B* and [Q,B] = -i A*. Thus B* = -i(QA - AQ) and A* = i(QB - BQ).
3. Substitute these formulas. Associativity and distributivity give
   AB* + B*A = -i(AQA - A²Q + QA² - AQA) = 0, and similarly BA* + A*B = 0.
4. The diagonal expansions give
   ΔA - ΔB = i(Q(AB + BA) - (AB + BA)Q) = 0.
5. Expand (A+B)(A*+B*) + (A*+B*)(A+B). The mixed terms are zero and the two
   diagonal terms agree, giving 2ΔB. Formal adjoints use only compact tests;
   the operator input is arbitrary. Zero, top and bottom degrees, dimension zero
   and the empty manifold are included by the actual alternating-tensor spaces. -/
theorem kahler_laplacian_identity
    (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
    [IsManifold (𝓘(ℂ, Model n)) ∞ M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    (g : HermitianMetric n M) (hclosed : IsKahlerMetric g)
    (μ : MetricVolume g) (D : FormalDolbeaultOperators g μ) :
    (D.dbar + D.del).comp D.dAdjoint + D.dAdjoint.comp (D.dbar + D.del) =
      (2 : ℂ) • (D.dbar.comp D.dbarAdjoint + D.dbarAdjoint.comp D.dbar) := by
  sorry

end ComplexManifold
