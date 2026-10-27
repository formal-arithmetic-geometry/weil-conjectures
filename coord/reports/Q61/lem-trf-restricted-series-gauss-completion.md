## Worker report

The module `Sheaf.RingTheory.RestrictedSeriesGaussCompletion` states
`RestrictedSeries.restricted_series_gauss_completion`, with its sole proof `sorry`.
No definition is duplicated or introduced; no dependency record is repaired and
no natural-language node field is changed. The module docstring accurately records
that BGR is unavailable and that the seven-step proof is Q42's explicit coefficient
argument, with ambient completeness supplied by the recorded Mathlib leaf. It does
not attribute this proof to an unverified book passage. I also read the current
blueprint's `lem-trf-local-term-locality` statement and proof: this analytic node is
an explicitly historical ingredient, not a replacement for its contracting route.

For the following clause matching, D_n means precisely the type printed repeatedly
in the signature: the coercion of
`MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ))`.
G_n means the existing expression `MvPowerSeries.gaussNorm (norm : F → ℝ)
(fun _ : Fin n ↦ 1)`. These abbreviations are explanatory prose only: the file has
no private aliases, local notation, local instances, hidden assumptions or lets.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Field with real multiplicative absolute value | `(F : Type u) [NormedField F]`; its `Field` parent is exactly `def-weil-field`, and its norm is real and multiplicative. |
| Nonarchimedean absolute value | `[IsUltrametricDist F]`; the distance is the one of the normed field. |
| Complete for the absolute-value distance | `[CompleteSpace F]`; no other topology on F is selected. |
| Every n >= 0 | All dimension binders are `(n : ℕ)`; the field universe `u` is arbitrary. |
| Restricted coefficients, addition and finite Cauchy product | D_n is exactly the dependency's Mathlib subring, at polyradius one. `IsRestricted` means norm-coefficients tend to zero in `cofinite`; inherited operations are the formal-series operations. No alternate ring operations are quantified. |
| Supremum norm finite | `∀ n f, MvPowerSeries.HasGaussNorm ... f.val`; this is boundedness above of the coefficient norm range, not merely a real supremum which defaults to zero when unbounded. At polyradius one all weights in `gaussNorm` are one. |
| Zero norm iff zero | First conjunction: `G_n f.val = 0 ↔ f = 0`. Nonnegativity is already the unconditional Mathlib `gaussNorm_nonneg` for the coefficient norm. |
| Norm of one | Second conjunction: `∀ n, G_n 1 = 1`. |
| Negation invariant | First conjunction: `G_n (-f).val = G_n f.val`. |
| Ultrametric addition inequality | Third conjunction: `G_n (f + g).val ≤ max (G_n f.val) (G_n g.val)`. |
| Submultiplication | Third conjunction: `G_n (f * g).val ≤ G_n f.val * G_n g.val`. |
| Complete metric is exactly the Gauss distance | Existential `M : ∀ n, MetricSpace D_n`, followed by `@dist _ (M n).toDist f g = G_n (f-g).val` and `∀ n, @CompleteSpace _ (M n).toUniformSpace`. The existential is a theorem conclusion, not an extra hypothesis or a chosen definition. `MetricSpace.ext` shows that the distance determines the structure uniquely. |
| Specified finite truncations converge in that metric | For every n and f, `∃ p : ℕ → D_n`, with `(p N).val = (MvPowerSeries.truncTotal (N+1) f.val).toMvPowerSeries` for every N and `Filter.Tendsto p Filter.atTop (@nhds _ (M n).toUniformSpace.toTopologicalSpace f)`. Mathlib's cutoff is strict, so N+1 retains exactly total degrees <= N, including constants for N=0. The values and convergence of this p are fully specified. |
| D_0=F | `Function.Bijective (constants F 0)` together with `∀ a, G_0 (constants F 0 a).val = ‖a‖`. Since `constants` is the existing ring hom, this is the ring identification and its original norm, without claiming literal type equality. |
| Every s >= 0 | Final `(s : ℕ)` includes s=0. |
| Series with coefficients a_i in D_s and row norms tending to zero | `∃ S : Subring (PowerSeries D_s)`, with membership iff `Filter.Tendsto (fun i ↦ G_s (PowerSeries.coeff i a).val) Filter.atTop (nhds 0)` for every formal series a. This fixes its carrier exactly. The subtype has inherited coefficientwise sum and finite Cauchy product. |
| Regrouping identifies D_(s+1) with those series as a ring | `∃ e : D_(s+1) ≃+* S`, whose every coefficient is fixed by the following coefficient equation. A ring equivalence includes surjectivity onto every restricted row series, injectivity and the specified inherited operations. |
| Grouping is by the last variable, not the first | For every f,i,μ the coefficient of μ in row i of `e f` is the coefficient of `Finsupp.equivFunOnFinite.symm (Fin.snoc (fun j ↦ μ j) i)` in f. The first s entries are μ and the last is i. |
| Target norm is supremum of row norms | `∀ f, G_(s+1) f.val = ⨆ i, G_s (PowerSeries.coeff i (e f).val).val`. Ring-equivalence surjectivity covers all target series. |
| Identification is isometric | `∀ f g, @dist _ (M (s+1)).toDist f g = ⨆ i, G_s (PowerSeries.coeff i ((e f).val - (e g).val)).val`. This is exactly the target supremum distance; it does not use the product topology. |
| Constants preserved | `∀ a : F, (e (constants F (s+1) a)).val = PowerSeries.C (constants F s a)`. |
| Multiplication by X preserved | Final universal equation: e applied to `⟨MvPowerSeries.X (Fin.last s), MvPowerSeries.isRestricted_monomial _ _ _⟩ * f` has underlying series `PowerSeries.X * (e f).val`. The membership proof is already Mathlib's theorem, so no assumed X or arbitrary shift map replaces the actual variable. |

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`, `Field`, via `NormedField` from
  `Mathlib.Analysis.Normed.Field.Basic` (field node's Mathlib match).
- `Sheaf.RingTheory.RestrictedSeriesPresentation`, `RestrictedSeries.constants`,
  plus its actual restricted-series subring and Gauss-norm interface. The other
  predicates in this dependency concern quotient presentations and are irrelevant
  to this node; the recorded leading declaration is not the whole interface.
- `Mathlib.RingTheory.MvPowerSeries.Restricted`, `MvPowerSeries.IsRestricted`,
  `MvPowerSeries.IsRestricted.subring`, `MvPowerSeries.isRestricted_monomial`.
- `Mathlib.RingTheory.MvPowerSeries.GaussNorm`, `MvPowerSeries.gaussNorm`,
  `MvPowerSeries.HasGaussNorm`; checked the signatures and docstrings of the
  individual inequality lemmas as well.
- `Mathlib.RingTheory.MvPowerSeries.Trunc`, `MvPowerSeries.truncTotal` and
  `coeff_truncTotal_eq_ite`; `Mathlib.RingTheory.PowerSeries.Basic`,
  `PowerSeries`, `PowerSeries.coeff`, `PowerSeries.C`, `PowerSeries.X`.
- Proof dependency `lem-trf-bounded-families-complete` is a Mathlib node:
  `Mathlib.Topology.ContinuousMap.Bounded.Basic`,
  `BoundedContinuousFunction.instMetricSpace`, `.dist_eq_iSup`,
  `.instCompleteSpace`. Their full signatures and docstrings were read; its
  module is a plain proof import, not an assumed Gauss completeness result.

Edge cases checked mathematically before writing: n=0 has the singleton multi-index
set, so every scalar is restricted and the Gauss norm is its coefficient norm.
At N=0 the truncation is exactly the constant term; for n=0 every truncation equals
f. For s=0 the snoc formula has only the last coordinate, giving ordinary restricted
univariate series. Zero series and the zero sequence satisfy the exact decay
predicate and norm formulas. The field is nonzero by `Field`; no zero-ring case is
accidentally claimed for F. Trivially normed complete fields are included: there is
no `NontriviallyNormedField` assumption, and their restricted series have finite
support, as expected. Finite fields and arbitrary characteristics are allowed.
Arbitrary epsilon-exceptional sets use cofinite convergence, not a coordinatewise
or total-degree topology. The cutoff set is finite since the dimension is finite.

Searches for an existing whole statement (all via prescribed `msearch.py`, saved
in the sandbox's `searches.jsonl`, plus direct source searches):

- LeanFinder: `Restricted series are complete for the Gauss norm and regrouping the
  last variable is an isometric ring equivalence`: 8 hits, chiefly Laurent-series
  adic completions, a polynomial Gauss lemma and Mahler equivalence; no exact match.
- Loogle: `"gaussNorm"`: 12 hits including `MvPowerSeries.gaussNorm`,
  `.HasGaussNorm`, `.gaussNorm_eq_zero_iff`, `.gaussNorm_add_le_max` and
  `.gaussNorm_mul_le`; these supply individual bounds, not this entire statement.
- Mathlib grep: `CompleteSpace|gaussNorm|finSucc` in `RingTheory/MvPowerSeries`:
  16 hits including the norm file, product-uniformity completeness and
  `MvPowerSeries.finSuccEquiv`. I opened the latter's complete signature,
  coefficient formula and docstring: it is an unrestricted formal-series
  equivalence grouping the first coordinate (`Finsupp.cons`). It gives neither
  the Gauss metric nor restrictedness; the last-coordinate snoc condition in
  our theorem is explicit rather than silently using its different convention.
- LeanSearch: `Restricted power series over a complete nonarchimedean normed field
  are complete for the Gauss norm and grouping the last variable is an isometric
  ring equivalence`: 8 hits, including `PowerSeries.IsRestricted`, Gauss norm
  lemmas and the two `WithPiTopology.instCompleteSpace` declarations. None says
  the full statement, and the latter completeness is for a different metric.
- `rg -n 'Gauss|gauss|RestrictedSeries|restricted.series'` in `lean/WeilConjectures`
  and `lean/Sheaf`, plus item-id and proposed-declaration searches in the upstream
  sources and `dag/lean_names_upstream.json`: no whole-statement match. Existing
  restricted-series presentation/affinoid modules use the same subring and norm;
  the affinoid comparison anticipates this completeness in its proof docstring
  but does not state this node. No new notion requires a new definition node.

No STATEMENT-DISPUTED flag or statement correction: no counterexample or missing
hypothesis was found. The node's source warning about unavailable BGR is retained.
The module has one named postponed theorem and no new definition, axiom or proof.

Validation: the prescribed scompile.py server check passed for both the sandbox
probe and the delivered library module, with no errors or unexpected warnings.
The initial compile found only the topology projection spelling: MetricSpace
exposes it through `.toUniformSpace.toTopologicalSpace`; this was corrected
without altering any mathematical clause. The node changes only `lean`, and its
recorded signature was compared exactly against the source. The prescribed deliver2.py --no-push dry run passed preflight and compilation
with OK. The delivery contains exactly the module, item node and worker report.

## Second reading by Q61

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
