## Worker report

The delivery states `EuclideanSpace.exists_dilatedCutoff_derivative_bounds` in
`Sheaf.Analysis.SymbolCutoffScaledDerivatives`. Its only proof is `sorry`; there are
no new definitions or nodes, dependency repairs, or statement corrections. The item's
node changes only in `lean`.

Hypothesis and conclusion correspondence:

- The usual real field is Mathlib `ℝ`; `m : ℕ` and `hm : 1 ≤ m` give exactly m ≥ 1.
  `EuclideanSpace ℝ (Fin m)` has the Euclidean norm, rather than the function-space
  supremum norm. The real-valued map is `θ : EuclideanSpace ℝ (Fin m) → ℝ`.
- Smoothness in Euclidean coordinates is `hθ : ContDiff ℝ ∞ θ`. The node speaks
  solely about the global Euclidean coordinate chart, so no auxiliary manifold,
  atlas, Hausdorffness, compactness, or second-countability hypothesis is imposed.
- `hzero` is θ = 0 at every point with norm ≤ 1, including the boundary; `hone`
  is θ = 1 at every point with norm ≥ 2, including that boundary. No positivity,
  monotonicity, radial symmetry, or bound between zero and one is added.
- The node's θ_R(ξ) = θ(ξ/R) is written inline as `θ (R⁻¹ • ξ)` throughout.
  Real scalar multiplication divides every Euclidean coordinate by R.
- The first conjunct gives `ContDiff ℝ ∞ (fun ξ ↦ θ (R⁻¹ • ξ))` for every R ≥ 1.
- The second conjunct is `∀ n : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ R : ℝ, 1 ≤ R → ...`.
  Thus A may depend on n, m, θ but cannot depend on R, γ, or ξ. Each multi-index
  is `γ : Fin m → ℕ`, its degree is `∑ j, γ j`, and the implication restricts it
  to total degree at most n. For every ξ the real absolute value (written as norm)
  is bounded by `A * (1 + R) ^ (-((∑ j, γ j) : ℤ))`, exactly the stated negative
  integer power, without replacing 1 + R by R.
- The multi-index derivative is `iteratedFDeriv ℝ k` applied to the list of coordinate
  vectors `EuclideanSpace.single j 1`, where coordinate j occurs γ j times, in
  increasing coordinate order. The flattened replicate-list length k is exactly
  ∑ j, γ j. For smooth functions this is the corresponding coordinate partial.
  This uses Mathlib's derivative directly, with no duplicate derivative definition.
- The third conjunct is the order-zero support assertion: for all R ≥ 1 and ξ
  with ‖ξ‖ ≤ R, the actual value θ(R⁻¹ • ξ) is zero.
- The fourth conjunct quantifies over every positive-degree γ (without the bound n)
  and every ξ outside the closed annulus, using
  `¬ (R ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * R)`. Its derivative is zero there. It neither forces
  zero at the annulus endpoints nor claims that the order-zero function vanishes
  outside the annulus.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`, with its full
  declaration and docstring read. The standard ℝ instance supplies this structure.
- `def-sfb-smooth-real-manifold`: Mathlib `ChartedSpace` and `IsManifold`, in
  `Mathlib.Geometry.Manifold.ChartedSpace` and
  `Mathlib.Geometry.Manifold.IsManifold.Basic`; signatures and docstrings read.
  Here the node explicitly specializes to smooth functions in Euclidean coordinates,
  so their coordinate smoothness is directly `ContDiff ℝ ∞`, imported publicly from
  `Mathlib.Analysis.Calculus.ContDiff.Basic`. No replacement manifold definition is needed.
- The Euclidean type, norm and coordinate unit vectors come from the public import
  `Mathlib.Analysis.InnerProductSpace.PiL2` (`EuclideanSpace`, its Euclidean norm
  formula, and `EuclideanSpace.single`). `iteratedFDeriv` is defined in
  `Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries`, publicly exposed by ContDiff.Basic;
  its definition and `iteratedFDeriv_zero_apply` were read.
- Proof dependency `lem-sfb-real-smooth-differentiation` uses Mathlib calculus,
  supplied by ContDiff.Basic; in particular its
  `ContinuousLinearMap.iteratedFDeriv_comp_right` signature and docstring were read.
- Proof dependency `lem-sfb-finite-dimensional-normed-proper` is
  `FiniteDimensional.proper`, Mathlib.Analysis.Normed.Module.FiniteDimension;
  its signature, context and docstring were read and its module is a proof import.
- Proof dependency `lem-sfb-compact-continuous-norm-bound` is the generated additive
  `IsCompact.exists_bound_of_continuousOn` in Mathlib.Analysis.Normed.Group.Bounded;
  its signature and additive-generation source were read and its module is a proof import.

The original source is explicitly marked unavailable locally in the node. The module
preserves that qualification and includes the full four-step agent proof recorded there:
chain rule and scaling, constant-region vanishing, finite compact-set bounds, and the
comparison R⁻ᵏ ≤ 2ⁿ(1+R)⁻ᵏ. It does not claim to have read the unavailable PDF.

Edge cases checked before writing: n = 0 only permits γ = 0; the replicate list is
empty and `iteratedFDeriv_zero_apply` gives the function itself. The bound remains
A ≥ 1 and does not incorrectly force global compact support. At γ > 0 there is no
support assertion inside the closed annulus or at its endpoints. R = 1 is included;
R = 0 is excluded by exactly the node's assumption. ξ = 0 lies in the zero region.
m = 1 uses the usual unit direction; m = 0 is excluded by the original node.
Arbitrarily large derivatives and R are allowed, and the support clause is not
restricted to one n. θ may overshoot between the two radii, so A is existential.
All variables are bound explicitly and `autoImplicit` is false.

Searches actually run (2026-10-24):

- msearch LeanFinder: "Derivative bounds for a dilated smooth cutoff theta(x/R),
  uniformly in R, with annular support". Eight hits, including ContDiffBump facts,
  Function.HasTemperateGrowth and SchwartzMap.decay. None states this estimate for
  an arbitrary cutoff with the given two constant regions.
- msearch Loogle: "iteratedFDeriv, ContinuousLinearMap". Twelve hits, including
  norm_iteratedFDeriv_one, iteratedFDeriv_one_apply and
  ContinuousLinearMap.iteratedFDeriv_comp_left; no exact statement.
- msearch grep in Analysis: "multiIndexPartialDeriv|iteratedFDeriv_comp_right|cutoff.*deriv".
  Four hits, with the composition formula in ContDiff.Basic and its applications;
  none gives all the cutoff assertions.
- msearch LeanSearch: "Uniform derivative bounds for a smooth cutoff theta(x/R),
  with derivatives supported in an annulus". Eight hits, including
  HasCompactSupport.iteratedFDeriv, ContDiffMapSupportedIn.bounded_iteratedFDeriv,
  ContDiffBump.toFun and temperate-growth bounds; no exact match.
- rg in lean/WeilConjectures and lean/Sheaf:
  "multiIndexPartialDeriv|cutoff.*[Dd]eriv|scaled.*[Dd]eriv". The existing
  EuclideanSpace.multiIndexPartialDeriv is complex-valued, so cannot directly take
  this node's real-valued θ. Its full declaration/docstring were read; it is not
  copied or specialized into a second definition. The real statement directly
  evaluates Mathlib iteratedFDeriv on unit directions, as the existing
  Sheaf.Analysis.SchwartzCutoffL2Approximation does for its derivatives.
  CutoffCauchyTransform concerns a different parameter derivative.
- rg of the exact item id in lean/WeilConjectures: no hits. rg of derivative names
  and owning module in dag/nodes confirmed the existing Fourier helper's ownership.

Validation: scompile.py compiled both its sandbox probe and the actual library module
cleanly (16.4 s and 1.5 s); no compiler errors or unexpected warnings.

## Second reading by Q131

Independent clause-by-clause reading done by the maintainer's review (cc reviewer, 2026-10-24).
It replaces the delivered section, which was a rereading by the same worker ("Dispatcher
instructions prohibit starting another agent; this is a separate rereading by the same worker").
No Lean or node change was needed.

Node clauses and their Lean rendering
(`EuclideanSpace.exists_dilatedCutoff_derivative_bounds`):

1. The real field [def-weil-field]: Mathlib `ℝ` (a `Field`). Correct.
2. Smooth functions in Euclidean coordinates [def-sfb-smooth-real-manifold]: on the model
   space `EuclideanSpace ℝ (Fin m)` (one global chart, `modelWithCornersSelf`), smoothness of a
   scalar function is `ContDiff ℝ ∞`; `∞` under `open scoped ContDiff` is `((⊤ : ℕ∞) : WithTop ℕ∞)`,
   i.e. C^∞, not analytic `ω`. Correct, no extra manifold hypotheses.
3. `m ≥ 1`: `(m : ℕ) (hm : 1 ≤ m)`. Correct; `m = 0` is excluded exactly as the node does.
4. `θ : ℝ^m → ℝ` smooth: `θ : EuclideanSpace ℝ (Fin m) → ℝ`, `hθ : ContDiff ℝ ∞ θ`. The norm
   of `EuclideanSpace` is the Euclidean norm `|ξ|`. Correct.
5. `θ = 0` on `{|ξ| ≤ 1}`: `hzero`, closed condition `‖ξ‖ ≤ 1`. Correct.
6. `θ = 1` on `{|ξ| ≥ 2}`: `hone`, `2 ≤ ‖ξ‖`. Correct. No range, monotonicity or radial
   hypothesis is added.
7. `θ_R(ξ) = θ(ξ/R)`, `R ≥ 1`: written inline `θ (R⁻¹ • ξ)` with `∀ R : ℝ, 1 ≤ R`. Correct.
8. `θ_R` smooth: first conjunct `∀ R, 1 ≤ R → ContDiff ℝ ∞ (fun ξ ↦ θ (R⁻¹ • ξ))`. Correct.
9. `∀ n ∃ A_n ≥ 1` depending only on `n, m, θ`: `∀ n : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ R ...`; `A` is
   chosen before `R`, `γ`, `ξ`, so it is uniform in them. Correct quantifier order.
10. Multi-index `γ`, `|γ| ≤ n`: `γ : Fin m → ℕ`, `(∑ j, γ j) ≤ n`. Correct.
11. `∂^γ θ_R(ξ)`: `iteratedFDeriv ℝ k θ_R ξ` evaluated on the list of unit vectors
    `EuclideanSpace.single j 1`, `j` repeated `γ j` times; `k` is the flattened length, which
    equals `∑ j, γ j`. For a C^∞ function the iterated Fréchet derivative is symmetric and its
    value on `(e_{j_1},…,e_{j_k})` is `∂_{j_1}⋯∂_{j_k}`, i.e. `∂^γ`; at `γ = 0` the list is empty
    and `iteratedFDeriv_zero_apply` gives `θ_R(ξ)` itself, not a zero derivative. Correct; no
    new derivative notion is defined (the existing `EuclideanSpace.multiIndexPartialDeriv` in
    `Sheaf.Analysis.L2WeakDerivativeFourierIdentity` is complex-valued and is a different
    encoding of the same operator; using Mathlib `iteratedFDeriv` directly is not a duplicate
    definition).
12. `|∂^γ θ_R(ξ)| ≤ A_n (1+R)^{-|γ|}`: `‖…‖ ≤ A * (1 + R) ^ (-((∑ j, γ j) : ℤ))`, zpow on ℝ,
    with `1 + R` (not `R`). Correct; the norm on ℝ is the absolute value.
13. `γ = 0`: `θ_R(ξ) = 0` for `|ξ| ≤ R`: third conjunct, closed condition. Correct (and true:
    `‖R⁻¹•ξ‖ ≤ 1`).
14. `|γ| > 0`: `∂^γ θ_R(ξ) = 0` unless `R ≤ |ξ| ≤ 2R`: fourth conjunct, `0 < ∑ j, γ j`,
    `¬ (R ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * R)`, all positive orders (not bounded by `n`). Correct; this is true
    since `θ_R` is locally constant on the open sets `‖ξ‖ < R` and `‖ξ‖ > 2R`.

Edge cases: `n = 0` (only `γ = 0`; bound is `sup |θ| ≤ A`, finite since `θ` is continuous on the
compact 2-ball and `= 1` outside); `R = 1`; `ξ = 0`; endpoints `‖ξ‖ = R` and `‖ξ‖ = 2R` (not
claimed zero for positive order, correctly); `θ` overshooting `[0,1]` (allowed, `A` existential);
`m = 1`. Universes: none (all types are concrete). No unbound variable (`autoImplicit false`).

Mathematics: the statement is true by the node's four-step proof (scaling identity
`∂^γ θ_R = R^{-|γ|}(∂^γθ)∘L_R`, local constancy, compact bound, `R^{-k} ≤ 2^n (1+R)^{-k}`).

Records and gates: the item node changes only in `lean`; `lean.statement` is verbatim the
signature in the file; module and declaration docstrings carry the source place (Demailly §3.7,
marked unavailable locally) and `(blueprint: lem-sfb-symbol-cutoff-scaled-derivatives)`; the
declaration docstring carries the four proof steps; proof is `sorry`; no definitions; no
pro-étale substitute; lines ≤ 100 characters. Both stmt_deps are Mathlib nodes; nothing else is
cited in the statement. Searches: `exists_dilatedCutoff`/`SymbolCutoff` in the project
`lean/` trees: only this module; no Mathlib declaration states the estimate.
