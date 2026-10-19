## Worker report

The module `Sheaf.AlgebraicGeometry.InvertibleKummerChartLogRegular` states
`AlgebraicGeometry.invertibleKummerChart_logRegular`. It uses the existing
`FineSaturatedLogScheme`, `EtaleLogHom`, and `FSLogChart` interfaces. The conclusion is
`X.IsLogRegular`, exactly the node's log-regularity conclusion.

The binders `(X Y : FineSaturatedLogScheme.{u})`, `f : EtaleLogHom X Y`, and
`hY : Y.IsLogRegular` render the morphism of locally Noetherian fs log schemes and the
log-regular target. The hypothesis `hcharts` quantifies over each source point and
chooses `c : FSLogChart f` with `x ∈ Set.range c.V.hom`; this is the etale-local source and
target chart neighbourhood. `FSLogChart` itself supplies the two fs monoids `c.P`, `c.Q`,
the chart maps, their compatibility, and the canonical comparison `c.comparison`.

The clause `Function.Injective c.g` renders injectivity of `h : P → Q`;
`Function.Injective c.groupMap` renders injectivity of `hᵍᵖ`. The clause
`∀ q, ∃ n, 0 < n ∧ ∃ p, c.g p = q ^ n` renders that every `q` has a positive
multiple in the image (multiplicative monoid notation). The following existential
renders a positive integer `n` killing the cokernel; `Finite c.cokernel` explicitly
renders its finiteness. The same existential requires the annihilator (`∀ z : c.cokernel, z ^ n = 1`)
to have image a unit at every point of the target chart neighbourhood
`c.W.left`. The final clause `Etale c.comparison` is the required etale comparison with
the canonical monoid-algebra fibre product. No regularity of the underlying source scheme
and no torsion-freeness conclusion is added.

Statement dependencies and declarations used are:

* `def-trf-fs-log-blowup`: `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`,
  `AlgebraicGeometry.FineSaturatedLogScheme`, `AlgebraicGeometry.EtaleLogHom`;
* `pqf-def-locnoeth`: Mathlib `AlgebraicGeometry.IsLocallyNoetherian`;
* `def-weil-etale-morphism`: Mathlib `AlgebraicGeometry.Etale`;
* `def-per-fs-log-smooth-etale`: `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`,
  `AlgebraicGeometry.FSLogChart`, `.groupMap`, `.cokernel`, and `.comparison`.
  This landed definition node was added to `stmt_deps` to record the chart interface used.

The proof plan is recorded in the theorem docstring. Its stated proof dependencies are
represented by imports where declarations exist: `IndEtaleStrictLocalInvariance`,
`FsFaceSharpening`, `LogRegularSharpChart`, `LogRegularCompletedChart`,
`FormalMonoidRingDimension`, `LocalCompletionQuotient`, `CompletionRegularLocal`,
`CompletionDimension`, `StrictHenselizationClosedImmersionCartesian`,
`StrictHenselizationRegular`, and `StrictHenselizationDimension`. The two Mathlib-only
proof dependencies use their recorded declarations without imports beyond the imported
Mathlib interfaces. `lem-per-completed-invertible-kummer-monoid-extension` is a postponed
proof dependency with no recorded Lean declaration; it is used only in the proof plan.

Edge cases checked: the source may be empty (the pointwise hypothesis is then vacuous);
`P` or `Q` may be the trivial monoid; the positive integer is required strictly positive;
`n = 1` is allowed; and nontrivial finite torsion cokernels are allowed provided their
order is a unit on the target chart. No torsion-free assumption is imposed.

Searches made: `msearch.py ... leanfinder "Invertible Kummer monoid charts with etale comparison preserve log regularity of fine saturated logarithmic schemes"` returned only ordinary etale/smooth declarations and no logarithmic statement; `msearch.py ... loogle '"LogRegular"'` returned zero hits; `msearch.py ... grep 'LogRegular|log_regular|Kummer.*chart'` returned zero hits. Repository and Mathlib `rg` searches for `Kummer`, `LogRegular`, and the item id found no duplicate statement. The existing `FSLogChart` and `EtaleLogHom` declarations were read in `Sheaf.AlgebraicGeometry.FSLogSmoothEtale` and used directly.

No `STATEMENT-DISPUTED` flag or node fault was found. The file compiles cleanly with `scompile.py`; the only expected diagnostic is the theorem's `sorry`.

## Second reading by NA

I reread the node, the module, and the `FSLogChart` declaration. The source/target objects,
local chart choice, fs chart data, compatibility, injective monoid map, injective group map,
Kummer positive-power condition, finite-cokernel annihilator, target-neighbourhood unit
condition, and etale canonical comparison each have an explicit counterpart above. The
conclusion is exactly `X.IsLogRegular`. No clause was dropped, and no underlying-scheme
regularity or torsion-free conclusion was introduced. The target unit condition is attached
to `c.W.left`, the target chart neighbourhood, rather than the source chart. The resumed self-check made cokernel finiteness explicit as `Finite c.cokernel`,
recorded the already landed chart-definition dependency, made proof-only imports ordinary
imports, expanded the six-step proof docstring, and removed the trailing `:=` from
`lean.statement` as required by the preflight diagnostic. The mathematical statement
and its conclusion are unchanged.
