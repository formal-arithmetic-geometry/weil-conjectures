## Worker report

The delivery states `PowerSeries.radius_le_radius_subst_exp` in
`Sheaf.Analysis.FormalExponentialRadius`, with its proof postponed by `sorry`.
It adds no definitions or hypotheses beyond the node's zero constant coefficient.
The node changes only in `lean`.

The source was read at
`literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-l-dl-a1-energy/sk-l-dl-a1-energy.proof.md`,
last paragraph: the convergent exponent series has a holomorphic exponential on the
same disk. The theorem isolates exactly the scalar absolute-convergence input.
Its docstring supplies all five steps of the node's finite-majorant proof.

Clause-by-clause correspondence:

- A complex formal power series `U(T)` is the binder `(U : PowerSeries ℂ)`.
  Mathlib's `PowerSeries` is the existing univariate `MvPowerSeries Unit`, with
  coefficientwise addition and the Cauchy product. There is no analytic-function
  replacement and no extra convergence assumption.
- Membership in `T ℂ[[T]]`, equivalently zero constant coefficient, is precisely
  `(hU : constantCoeff U = 0)`. Coefficients in degrees at least one are otherwise
  unrestricted complex numbers. No positivity or positive radius is assumed.
- The series `E(T) = exp(U(T)) = ∑ r, U(T)^r/r!` is the actual term
  `subst U (exp ℂ)`. The first explicit argument of `PowerSeries.subst` is the
  series substituted for the variable; the second is the outer exponential
  series. This is also Mathlib's `(PowerSeries.exp ℂ).subst U` notation.
  `PowerSeries.coeff_exp` gives the rational coefficient `1/r!`, and
  `PowerSeries.HasSubst.of_constantCoeff_zero' hU` makes the substitution
  coefficientwise finite. Because the order of `U` is at least one, terms with
  `r > N` vanish in degree `N`, giving exactly the stated finite coefficient
  convention and constant coefficient one. No separate binder for `E` is needed
  because the canonical construction is substituted into the conclusion.
- Both absolute convergence radii are the dependency's `PowerSeries.radius`,
  taking values in `ℝ≥0∞`. The conclusion
  `U.radius ≤ PowerSeries.radius (subst U (exp ℂ))` is exactly `R(E) ≥ R(U)`.
  The existing radius definition agrees with the admissible-radius supremum:
  `summable_norm_coeff_mul_pow` gives summability below the radius, and
  `le_radius_of_summable` bounds the radius from summability. No convergence at
  the supremum is required.

Dependency declarations read and used:

- `def-weil-formal-power-series`: Mathlib `PowerSeries`, from
  `Mathlib.RingTheory.PowerSeries.Basic`, imported by the exponential and
  substitution modules. The declaration and coefficient map were read.
- `def-weil-power-series-exponential`: Mathlib `PowerSeries.exp` from
  `Mathlib.RingTheory.PowerSeries.Exp`, specialized by `PowerSeries.subst` from
  `Mathlib.RingTheory.PowerSeries.Substitution`. I read their full declarations,
  docstrings, `coeff_exp`, `constantCoeff_exp`, `HasSubst.of_constantCoeff_zero'`,
  and the finite-support and coefficient substitution formulas. The dependency's
  recorded specialization is usable without any repaired interface.
- `d-real-series`: `PowerSeries.radius` from
  `WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius`. I read its full
  definition and docstring, plus the two summability/radius lemmas above. The
  nonnegative-coefficients predicate recorded on that node is not needed here.
- Proof input `def-weil-complex-absolute-value`: `Complex.instNorm` and
  `Complex.norm_def` from `Mathlib.Analysis.Complex.Norm`, already provided by
  the radius module and also imported explicitly for the proof plan.
- Proof input `lem-dl-a1-real-factorial-series-summable`:
  `Real.summable_pow_div_factorial (x : ℝ)` from
  `Mathlib.Analysis.SpecificLimits.Normed`, imported as a proof dependency.
- Proof input `lem-dl-a1-nonnegative-series-partial-sums`:
  `Summable.sum_le_tsum` (additive version of `Multipliable.prod_le_tprod`) from
  `Mathlib.Topology.Algebra.InfiniteSum.Order`, and
  `summable_of_sum_range_le` from `Mathlib.Topology.Algebra.InfiniteSum.Real`.
  Both modules are imported as proof dependencies; the full source signatures
  were read. All proof-dependency nodes already have their declarations as
  recorded exact Mathlib matches or upstream definitions.

Edge cases checked mathematically before writing:

- `U = 0` gives `E = 1`, both of infinite radius.
- `U = X` gives the usual entire exponential, also infinite radius.
- A series of radius zero is allowed: the claimed inequality is the minimum
  radius bound, not an assertion of positive convergence radius.
- Infinite input radius forces infinite output radius; the extended nonnegative
  real codomain retains this case without a finiteness assumption.
- `U = X/(1-X)` is permitted and has radius one; convergence is required only
  in smaller disks. Arbitrary complex coefficients and cancellation remain
  permitted, so the output radius may be strictly larger.
- The majorant proof includes `t = 0`, `N = 0`, the empty tuple in power zero,
  and the empty partial sum. The zero constant coefficient is essential to the
  finite formal substitution and is an explicit, nonvacuous hypothesis.
- No universe is free or auto-bound: the only underlying coefficient type is
  the fixed complex field. The two mathematical binders are explicit.

Searches for an existing exact theorem (2026-10-18):

- `msearch.py ... leansearch` query: “The formal exponential of a complex power
  series with zero constant term has convergence radius at least the original
  radius”. Result: eight hits, including
  `NormedSpace.expSeries_radius_eq_top`,
  `NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos`,
  `NormedSpace.expSeries_hasSum_exp_of_mem_ball'`, and
  `HasFPowerSeriesOnBall.r_le`. These concern an analytic exponential or a
  formal multilinear series and do not give the scalar substitution inequality.
- `msearch.py ... leanfinder` query: “A complex formal power series with zero
  constant coefficient has formal exponential with at least the same convergence
  radius”. Result: eight exponential-function hits, including
  `NormedSpace.expSeries_radius_eq_top`, `NormedSpace.expSeries_radius_pos`,
  `NormedSpace.exp_hasFPowerSeriesOnBall`, and exponential sum identities.
  None states this theorem for `PowerSeries.radius` and formal substitution.
- `msearch.py ... loogle` query: `"radius", "exp"`. Result: nine hits, the
  exponential multilinear-series radius, expansion/derivative theorems, and
  `UpperHalfPlane.qExpansionFormalMultilinearSeries_radius`. No exact match.
- `msearch.py ... grep` query:
  `(exp|subst).*(radius|summable)|(radius|summable).*(exp|subst)` in
  `RingTheory/PowerSeries`. Result: three hits, `subst_tsum`, `summable_subst`,
  and its conclusion in `Substitution.lean`. These are substitution-continuity
  statements, not the scalar absolute-convergence radius estimate.
- Direct `rg` with that same regular expression and the item id over
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's
  `lean/Sheaf`: one unrelated `le_radius_of_bound` application in
  `EtaleCohomology/Purity/RealSheaves/Semicontinuity.lean`; no exact theorem and
  no upstream item marker. The corresponding item-id search has no hit.
- Direct `rg` over all Mathlib and `dag/lean_names_upstream.json` for
  `radius_le_radius.*exp`, `radius_exp`, `exp_radius`, and `le_radius.*subst`:
  no hit. A second name-collision search for `radius_le_radius_subst_exp` and
  related candidate names over the index, Mathlib, upstream, and `lean/Sheaf`
  also has no hit.

No statement correction, new node, dependency repair, or disputed statement was
necessary. Compilation and delivery-preflight results are recorded below.

## Second reading by N4

Author self-check under the direct-delivery brief; independent mathematical review
is left to the maintainer. I reopened the node and the finished Lean module and
matched the type `PowerSeries ℂ`, the single equality `constantCoeff U = 0`, the
canonical finite exponential `subst U (exp ℂ)`, and the oriented radius inequality
against every clause of the statement. The coefficient construction is the
recorded Mathlib specialization, and the radius is the recorded upstream
notion, with neither positivity nor finite-radius restrictions. The theorem's
proof docstring accounts for every listed proof step and both endpoints. The
imports include all already-stated proof dependencies. Compilation required spelling the output radius as
`PowerSeries.radius (subst U (exp ℂ))` because field notation on the substitution
result resolves through the underlying function type; a type annotation alone
did not fix field resolution. This changes no object or hypothesis. No semantic mismatch was found and no statement
or dependency field was changed.

Validation: `scompile.py N4 lem-dl-a1-formal-exponential-radius` compiled the final
file successfully both as a sandbox module and at its library module path, with
no diagnostics (1.6 s and 1.7 s respectively). The earlier field-notation errors
were repaired as described above. A source check found no line over 100 columns,
and comparing the node copy with the shared base showed only `lean` changed.

Delivery dry run: `deliver2.py N4 lem-dl-a1-formal-exponential-radius --no-push`
printed `OK (dry run): commit 090ee41d05 passes the preflight and compiles;
nothing pushed`. The checked package contains exactly this report, the item
node, and its single Lean module.
