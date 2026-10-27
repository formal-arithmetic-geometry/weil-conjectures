## Worker report

The module `Sheaf.Geometry.Manifold.ChartAbsoluteJacobianCocycle` defines
`OpenPartialHomeomorph.chartAbsoluteJacobian` and states
`OpenPartialHomeomorph.chartAbsoluteJacobian_cocycle`. The definition has actual data;
the theorem's entire proof is `sorry`. No other theorem is postponed.

Hypothesis and clause correspondence:

- The dimension is `{m : ℕ}`, including zero. The manifold is `{N : Type u}` with
  `[TopologicalSpace N]`, `[ChartedSpace (EuclideanSpace ℝ (Fin m)) N]`, and
  `[IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m))) ∞ N]`.
  The self model is all of Euclidean space, without boundary or corners.
  There are no orientation, Hausdorff, second countability, compactness, or
  nonemptiness hypotheses. Universe `u` is explicitly declared and unrestricted.
- Each chart is an `OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m))`.
  Its source and target are open and its inverse is `symm`. The assumptions `hx`,
  `hy`, and the quantified membership assumption on `z` put the charts in
  `IsManifold.maximalAtlas` of this smooth structure: every compatible chart is
  admitted, including charts outside the original atlas.
- The defined function is exactly
  `|Matrix.det (fun a b : Fin m ↦
    (fderiv ℝ (fun q ↦ y (x.symm q)) (x p) (EuclideanSpace.single b 1)) a)|`.
  Thus the transition is `y ∘ x.symm`, its ordinary real Frechet derivative is
  evaluated at `x p`, column `b` is its value on the standard basis vector, and
  row `a` extracts the `a`-coordinate. This uses neither manifold differentiation
  nor differentiation within a closed set. Only values on the open overlap are
  asserted. `Matrix.det` already sets the empty determinant to one.
- The first conjunct is `ContMDiffOn ... ∞ (x.chartAbsoluteJacobian y)
  (x.source ∩ y.source)`, exactly manifold smoothness on the overlap.
- The second is `∀ p ∈ x.source ∩ y.source, 0 < x.chartAbsoluteJacobian y p`.
- The third is the same `ContMDiffOn` assertion for
  `fun p ↦ (x.chartAbsoluteJacobian y p)⁻¹`.
- The fourth states `∀ p ∈ x.source, x.chartAbsoluteJacobian x p = 1`.
- The fifth states the reverse-pair product
  `y.chartAbsoluteJacobian x p * x.chartAbsoluteJacobian y p = 1` on the overlap.
- The sixth quantifies over every compatible chart `z` and every
  `p ∈ x.source ∩ y.source ∩ z.source`, asserting
  `x.chartAbsoluteJacobian z p =
    y.chartAbsoluteJacobian z p * x.chartAbsoluteJacobian y p`.
  Quantifying over arbitrary `x,y` gives all diagonal and inverse identities;
  the extra universally quantified `z` gives every triple identity. This does
  not require a nonempty or universe-restricted indexing family of charts.

Dependencies read and used:

- `def-sfb-smooth-real-manifold` is a Mathlib leaf, with recorded match
  `ChartedSpace` in `Mathlib.Geometry.Manifold.ChartedSpace` and `IsManifold`
  in `Mathlib.Geometry.Manifold.IsManifold.Basic`. Their complete class
  signatures were read. `IsManifold.maximalAtlas` in the latter module gives
  compatibility with the atlas. These are publicly exposed through
  `Mathlib.Geometry.Manifold.ContMDiff.Defs`, which supplies `ContMDiffOn`.
- `def-weil-pbc-matrix-determinant` records `Matrix.det` in
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, imported publicly.
  The definition, `det_apply`, and `det_isEmpty` were read: the formula and its
  column convention agree exactly with the node.
- Proof dependency `lem-sfb-real-smooth-differentiation` is recorded on Mathlib
  calculus declarations, including `ContDiffAt.comp`,
  `ContDiffAt.fderiv_right`, `ContDiffAt.differentiableAt`, constant and linear
  smoothness, addition/multiplication, and `HasFDerivAt.comp`. Their relevant
  signatures were read. `Mathlib.Analysis.Calculus.ContDiff.Comp` is a plain
  proof import. The logarithm clause of that bundled leaf is not used here.
- Proof dependency `lem-sfb-matrix-cramer-determinant-identities` is recorded
  on `Matrix.det_mul`, `Matrix.det_adjugate`, and
  `Matrix.cramer_eq_adjugate_mulVec`; the multiplicativity clause is used here.
  `Mathlib.LinearAlgebra.Matrix.Adjugate` is its plain proof import, while
  `det_mul` is already available from the public determinant dependency.
- `Mathlib.Analysis.InnerProductSpace.PiL2` supplies the specified
  `EuclideanSpace` and its standard vectors, not another definition of them.

Edge cases checked before writing: at `m = 0` the coordinate matrix has index
`Fin 0`, so its determinant is one independently of the derivative. The absolute
value and reciprocal are also one. Empty manifolds, empty chart sources and empty
pair/triple overlaps are admitted; the pointwise clauses become vacuous and
smoothness on the empty set imposes no restriction. There is no lower bound on
dimension, no chosen chart index, and no extra global topological hypothesis.
The matrix row/column convention was checked against the standard basis and
the cocycle order against `x → y → z`.

Searches for an existing declaration:

- `msearch.py ... leanfinder` with query
  `Absolute determinants of smooth manifold chart transition derivatives are smooth
  positive and satisfy the multiplicative cocycle identity`: eight hits, including
  vector-bundle `ContMDiff.coordChange`, `ContMDiffOn.coordChange`,
  `contMDiffOn_coordChangeL`, and `contDiffOn_fderiv_coord_change` in
  `Mathlib.Geometry.Manifold.VectorBundle.Tangent`. The latter signature was
  opened: it proves regularity of a derivative for atlas charts, not determinant
  positivity, reciprocal smoothness or cocycle identities for compatible charts.
- `msearch.py ... loogle '"det", "fderiv"'`: twelve hits, all from
  `Mathlib.MeasureTheory.Function.Jacobian`, concerning measurability or change
  of variables; none is this chart-cocycle statement.
- `msearch.py ... grep 'abs.*(jacobian|[Dd]et)|([Jj]acobian|[Dd]et).*cocycle'
  Geometry`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `absoluteJacobian|abs.*[Jj]acobian|chart.*[Jj]acobian|[Jj]acobian.*cocycle|lem-sfb-chart-absolute-jacobian-cocycle`
  found only unrelated algebraic Jacobian documentation. A broader declaration
  search found algebraic/formal Jacobians, not this notion.
- The exact names `chartAbsoluteJacobian` and `ChartAbsoluteJacobianCocycle`
  were searched in `dag/lean_names_upstream.json`, Mathlib, `WeilConjectures`,
  and `Sheaf`: no matches. The search wrapper retains its raw responses in
  `searches.jsonl` in this sandbox.

No new independent notion, dependency repair, statement correction, or
STATEMENT-DISPUTED issue was needed. The source record explicitly describes an
agent-stated well-definedness lemma and marks the Demailly PDF unavailable;
this delivery preserves that limitation and does not claim to have read it.
The six-step proof is reproduced in the theorem's docstring from the node.

Validation: the prescribed `scompile.py Q33 lem-sfb-chart-absolute-jacobian-cocycle`
compiled this file as sandbox and library modules on the server, both cleanly,
in 1.8 seconds each. All variables and the universe are explicitly bound;
`autoImplicit` is disabled in the file. The prescribed `deliver2.py ... --no-push`
returned `OK (dry run): commit 0520e21fd06 passes the preflight and compiles;
nothing pushed` on 2026-10-24.

## Second reading by Q33

I reread the node and the completed Lean file directly; this is a worker
self-check, with the independent delivery review left to the maintainer as
specified by the dispatch brief. The dimension-zero case is retained by
`Fin m`, the model is the boundaryless `modelWithCornersSelf`, and no separation
or countability assumption appears. The derivative expression was checked to
use `y (x.symm q)` at `x p`, with output-coordinate rows and input-vector
columns. The six conjuncts appear in the node's order, with the same pair and
triple overlap domains and the same order of the multiplicative factors.
`maximalAtlas` membership is required for all three arbitrary charts, so the
statement covers compatible charts rather than only the chosen atlas. No
mismatch was found and no node statement changed. The helper definition is
the actual function introduced by this item, not an extra hypothesis or a
separate replacement for the dependency notions.
