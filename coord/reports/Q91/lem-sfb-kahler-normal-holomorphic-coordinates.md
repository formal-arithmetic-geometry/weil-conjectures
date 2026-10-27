## Worker report

The delivered theorem is `ComplexManifold.exists_kahler_normal_holomorphic_coordinates` in
`Sheaf.Geometry.Manifold.KahlerNormalHolomorphicCoordinates`. It states the accepted node
without changing its natural-language statement or proof. Its only proof is `sorry`.
The companion definition module `Sheaf.Geometry.Manifold.KahlerCoordinateData` contains
six explicit definitions and no postponed proofs or existence choices.

The inherited BLOCKED ending was a stage-1 duplicate-split refusal. The current node is
split, reviewed by Q21, has no Lean record, and appears at stage 2 in coord/queue.tsv.
The stage handoff in coord/brief-stage2.md §0 expressly allows its stage-2 statement.
No repair note for this item exists. The earlier reviewed split is preserved.

Hypotheses and clauses, matched individually:

- The usual real and complex fields are Mathlib `ℝ` and `ℂ`. The sole original statement
  dependency, def-weil-field, is Mathlib's `Field` class (Algebra/Field/Defs.lean:180).
  The class's full signature and documentation were read; no field notion is redefined.
- The dimension is `(n : ℕ) (hn : 1 ≤ n)`. Its index set is `Fin n`, reindexing the
  node's indices 1 through n without changing their number.
- The complex manifold is `(M : Type u) [TopologicalSpace M]
  [ChartedSpace (Model n) M] [IsManifold (𝓘(ℂ, Model n)) ∞ M]`.
  `Model n = Fin n → ℂ`, and the identity model with corners has no boundary.
  The complex structure acts by `Complex.I • v`. The local result needs no global
  compactness, connectivity, countability, or choice of a global metric topology.
- The smooth positive definite Hermitian metric is `(h : HermitianMetric n M)`, reusing
  the landed def-sfb-hermitian-dolbeault-data. Its `matrix`, `hermitian`, `positive` and
  `smooth` fields were read in full. The existing `metricPair` is conjugate-linear first;
  `chartHermitianPair h e z v w` reverses its arguments, after the actual `chartTangent`
  pullback, to implement precisely the node's first-linear convention.
- `g = Re h` is used in `chartFundamentalForm h e z v w`, defined as
  `(chartHermitianPair h e z (Complex.I • v) w).re`. Thus the real form is exactly
  `ω(v,w)=g(Jv,w)`, also equal to `-Im h(v,w)`.
- The hypothesis `(hclosed : IsKahlerMetric h)` is the coordinate definition of
  `dω=0`: the real directional derivative cyclic sum on every holomorphic chart target
  vanishes for every triple of constant real vectors. This is not a new arbitrary
  form, a supplied isomorphism, or an assumption of the desired normal coordinates.
- The point is arbitrary `(a : M)`. The conclusion supplies an
  `OpenPartialHomeomorph M (Model n)`, whose source and target are open and whose maps
  are continuous mutual inverses there. Membership in
  `IsManifold.maximalAtlas (𝓘(ℂ, Model n)) ∞ M` says that its transition maps and their
  inverses are complex smooth, hence holomorphic. It includes every compatible
  biholomorphic coordinate chart, not just the preferred initial atlas.
- `a ∈ e.source` and `e a = 0` give the neighborhood of a and the centering.
- `chartHermitianCoefficient h e j k z` is exactly
  `h(∂x_j,∂x_k)` in this chart, with the actual tangent coordinate change.
- The first quantified conjunct, for every `z ∈ e.target` and `v w : Model n`, is
  the identity `ω = (i/2) Σ H_{j bar k} dz_j ∧ dbar_z_k` evaluated on arbitrary real
  tangent vectors: the wedge evaluates to `v j * star (w k) - w j * star (v k)`.
  Equality on every pair of real vectors is equality of these two-forms, and the
  left-hand real value is embedded in ℂ for the identity. It holds on the whole chart.
- `∀ j k, chartHermitianCoefficient h e j k 0 = if j = k then 1 else 0` gives
  the identity matrix at a, since `e a = 0` and a is in the chart source.
- For every `j k l`, the last conjunction sets both `wirtingerPartial` and
  `wirtingerBarPartial` of that same coefficient to zero at 0. The former is
  `(D_ℝ f(e_l) - i D_ℝ f(i e_l))/2` and the latter has the plus sign, exactly the
  node's two operators. These are real derivatives within the open target;
  they are not complex derivatives of a potentially nonholomorphic metric coefficient.
  Since 0 lies in the target, arbitrary extensions off the target do not affect them.

Dependency declarations used:

- Mathlib.Algebra.Field.Defs: `Field`; the actual real/complex fields come through the
  existing Hermitian data's public Mathlib imports.
- Sheaf.Geometry.Manifold.HermitianDolbeaultData (landed definition node newly added
  to stmt_deps): `ComplexManifold.Model`, `HermitianMetric`, `metricPair`, `chartTangent`,
  `realCoordinateVector`. Their full definitions and documentation were read.
- Sheaf.Geometry.Manifold.KahlerCoordinateData (new definition node, newly added to
  stmt_deps): all six declarations listed in its lean.declarations.
- Mathlib.Geometry.Manifold.IsManifold.Basic: `IsManifold.maximalAtlas`, whose full
  definition is the maximal atlas of `contDiffGroupoid` for this model and regularity.
- The two proof-dependency Mathlib matches were read, with their source signatures:
  `stdOrthonormalBasis` in Mathlib.Analysis.InnerProductSpace.PiL2;
  `AnalyticAt.hasStrictFDerivAt` and `OpenPartialHomeomorph.analyticAt_symm'` in
  Mathlib.Analysis.Calculus.FDeriv.Analytic;
  `HasStrictFDerivAt.toOpenPartialHomeomorph`, its coe and source membership in
  Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv;
  `AnalyticAt.exists_ball_analyticOnNhd` in Mathlib.Analysis.Analytic.ChangeOrigin.
  Their modules are plain proof imports. The theorem docstring preserves all four
  accepted proof steps: orthonormal normalization, closedness symmetry, quadratic
  inverse chart, and explicit metric first-jet cancellation and conjugation.

Edge cases checked mathematically before delivery:

- n=1: for the unit metric, h(v,w)=v conjugate(w), ω(1,i)=1. The wedge formula evaluates
  to `(i/2)(-2i)=1`, checking the sign, coefficient and factor 1/2. In this dimension
  every smooth Hermitian fundamental form is closed; the symmetric quadratic term
  cancels the one complex first derivative, and Hermitian symmetry cancels its conjugate.
- A nonreal off-diagonal coefficient H_12=i, H_21=-i gives ω(e_1,e_2)=-1 from both
  definitions. This checks that the argument reversal did not transpose the stated
  first-linear coefficient matrix or change the sign.
- Closedness is a substantive hypothesis in dimension two: the positive metric
  diag(exp(x_2),1) has ω=exp(x_2) dx_1∧dy_1 + dx_2∧dy_2 and nonzero derivative
  exp(x_2) dx_2∧dx_1∧dy_1. The cyclic closedness test detects this triple.
- n=0 is excluded by the node and by hn, although all six helper definitions still
  make sense in dimension zero. No Nonempty (Fin n) instance is introduced.
- An empty manifold has no a, so the pointwise statement is vacuous as intended.
  The chart in the conclusion cannot have empty source because it contains a.
- The metric may have nonzero curvature. Only its first jet, not second derivatives
  or the entire matrix function on the neighborhood, is normalized.
- M lives in unrestricted universe u. The fixed finite-dimensional coordinate model
  is the ordinary complex vector space; no bound is imposed on the point universe.

Searches run (actual tool answers, also recorded in the new node):

- msearch leansearch: `Holomorphic coordinate charts of a complex manifold Hermitian metric
  fundamental two form Wirtinger partial derivatives`: eight hits, namely two-dimensional
  Kahler pairings, complex conformal/differentiability facts, preferred-chart differentiability,
  a one-variable harmonic derivative and the upper half-plane charted structure. No match.
- msearch leanfinder: `A smooth positive Hermitian metric on a complex manifold with closed
  fundamental two form admits holomorphic coordinates normal to first order`: eight hits
  about real Riemannian metrics and local estimates; no match.
- msearch loogle: `IsManifold, ContMDiff, Hermitian`: zero hits, with unknown identifier
  Hermitian. This failed pattern is not treated as evidence of absence.
- msearch grep: `HermitianMetric|normalHolomorphic|KahlerManifold|KaehlerManifold`: zero
  Mathlib hits. Additional Mathlib manifold greps for the coordinate constructions found none.
- rg in both lean/WeilConjectures and lean/Sheaf for `HermitianMetric` and related chart
  names found the landed HermitianDolbeaultData implementation. Searches for
  `chartHermitianPair|chartFundamental|wirtingerPartial|IsKahlerMetric` returned no hits.
  The exact item-id search in lean/WeilConjectures also returned no declaration.
- DAG definition-statement search for Hermitian metric / fundamental form / Wirtinger
  found only def-sfb-hermitian-dolbeault-data, which is reused. Whole-blueprint searches
  for Hermitian, Wirtinger, and normal holomorphic returned zero matches; Kähler returned
  only algebraic-differential statements. The item's blueprint ancestor is null, as on base.

Source checked directly: Kong's online PDF, Definition 3.18 and Theorem 3.19 on PDF page 7,
plus the Wirtinger convention in §2.1. The source defines ω=-Im h and g=Re h and gives
ω=g(J-,-), with coefficient factor i/2. The stage-1 review had already reconciled this
first-linear convention; this delivery retains it. No STATEMENT-DISPUTED issue or statement
correction was needed.

Validation: both modules compiled individually in dependency order using scompile.py,
against the live published build. The initial name-resolution error for maximalAtlas was
fixed by its full name IsManifold.maximalAtlas. The final compile had no errors or warnings.
No global build or direct Git command was run.

## New nodes

`def-sfb-kahler-coordinate-data` defines only the missing coordinate calculus associated
to the existing Hermitian metric: first-linear pullback pairing, metric coefficients,
real fundamental form, its closedness, and the two real Wirtinger operators. The source
is Kong §2.1 and §3.3 Definition 3.18, not a normal-coordinate existence theorem. Mathlib,
project and DAG searches above found no existing version of this calculus. The metric,
tangent transition, real coordinate basis and holomorphic atlas are all reused. Its module
contains actual formulas with no sorry, arbitrary map, or choice from mere existence.

The current latest blueprint direct-image statement and proof were also read. Its route
now uses compactification; the accepted analytic supporting chain has no blueprint-is
attachment and is left unchanged. The new definition inherits the null ancestor and
existing via chain rather than claiming to be a current blueprint unit.

The first dry run compiled both modules and reached server preflight. It required
`import_flags` on the new definition node; an empty list was added to satisfy the current
node schema. No mathematical field or Lean declaration changed.

## Second reading by Q91

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
