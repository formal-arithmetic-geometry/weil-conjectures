## Worker report

The module `Sheaf.TraceFormula.MinimalJacobianBinaryHypersurface` states
`MvPowerSeries.minimalJacobian_binaryHypersurface`. Its single proof is `sorry`.
It introduces no definitions. The statement and proof plan were read against
Stacks Project `curves.tex`, Tag 0C4C, from the block-minor bound to the final
quadratic calculation, and Tag 0C48(2) for principality. No node correction or
statement dispute is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The arbitrary field is `(F : Type u) [Field F]`; `e s : ℕ` allow both zero
  variables and zero generators. The ambient ring is `MvPowerSeries (Fin e) F`.
- The finite generators are `h : Fin s → MvPowerSeries (Fin e) F`, with
  `hgen : H = Ideal.span (Set.range h)` specifying the ideal `H` in the node.
- The variables' ideal `𝔭` is written directly as
  `Ideal.span (Set.range (X : Fin e → MvPowerSeries (Fin e) F))`.
  `hminimal` is exactly `H ≤ 𝔭 ^ 2`.
- `R` is the actual ideal quotient `MvPowerSeries (Fin e) F ⧸ H`.
  `𝔪 = 𝔭/H` is `Ideal.map (Ideal.Quotient.mk H) 𝔭`.
- The matrix in `hjacobian` has entry
  `Ideal.Quotient.mk H (pderiv F i (h j))`, with `Fin e` rows and `Fin s`
  columns. Taking determinants after reducing the entries gives the images of
  the original determinants, since the determinant is a polynomial in entries.
- `D` is the existing `Matrix.minorIdeal e s (e - 1)` of this matrix. For
  `e = 0` and `e = 1`, `e - 1 = 0`, so the unique empty minor is `1` and
  `D = ⊤`, precisely the stipulated convention `D = R`. When `e ≥ 2` and
  `s < e - 1`, the column-subset indexing type is empty, giving `D = ⊥`.
  This uses the existing `def-trf-minor-ideal`, added to `stmt_deps`.
- `hdepth` is `Ideal.depth 𝔪 R = (1 : ℕ∞)`. Because `H ≤ 𝔭²`, the image
  `𝔪` is the proper maximal ideal; the recorded `IsLocalRing.depth` is
  defined as exactly `Ideal.depth` at that ideal. Writing the ideal explicitly
  avoids imposing any additional typeclass assumption on the quotient.
- `hjacobian` is the required equality `D = 𝔪`.
- The first existential witness `he : e = 2` is the conclusion `e = 2`.
  `Fin.cast he.symm 0` and `Fin.cast he.symm 1` are indices in the ORIGINAL
  `Fin e`; they are the first and second coordinates, without transporting
  the ideal, equation, or quotient to a different ring. Thus `u` and `v` below
  mean `X (Fin.cast he.symm 0)` and `X (Fin.cast he.symm 1)`.
- The witnesses `f : MvPowerSeries (Fin e) F` and `a b c : F` and the first
  three conjuncts state `f ≠ 0`, `f ∈ 𝔭² = (u,v)²`, and `H = Ideal.span {f}`.
- `homogeneousComponent 2 f = C a * u ^ 2 + C b * (u * v) + C c * v ^ 2`
  states the complete homogeneous quadratic part, not merely selected
  coefficients. Its three distinct coefficients are necessarily `a,b,c`.
- `b ^ 2 - 4 * a * c ≠ 0` is the stated discriminant condition.
- The next conjunct repeats the same `Matrix.minorIdeal` expression for `D`
  and equates it to `Ideal.span` of the quotient classes of `pderiv F i f`
  at the two indicated indices.
- The last two conjuncts give `homogeneousComponent 1` of these derivatives
  as `C (2 * a) * u + C b * v` and `C b * u + C (2 * c) * v`.
- There is no characteristic assumption: in particular the coefficients `2`
  and `4` are interpreted in `F`, including characteristic two.

Dependency declarations read and used:

- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `MvPowerSeries.X`,
  `MvPowerSeries.C`; the recorded power-series notion.
- `Mathlib.LinearAlgebra.Matrix.Defs`: `Matrix`.
- `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`: `Matrix.det`, used inside
  the recorded minor ideal.
- `Mathlib.RingTheory.MvPowerSeries.Derivative`: `MvPowerSeries.pderiv`, the
  recorded Mathlib match for the derivative node. Its coefficient formula and
  derivation signature were read in full.
- `WeilConjectures.RingTheory.Depth`: `Ideal.depth` and `IsLocalRing.depth`.
- `Sheaf.LinearAlgebra.Matrix.MinorIdeal`: `Matrix.minorIdeal`, read together
  with its node. The actual data is a span over pairs of increasing row and
  column subsets, giving exactly the conventions needed here.
- `Mathlib.RingTheory.MvPowerSeries.Order`: `MvPowerSeries.homogeneousComponent`;
  `Mathlib.RingTheory.Ideal.Quotient.Operations`: the actual quotient and map.
- Proof-only imports: `WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete`
  (`MvPowerSeries.power_series_field_cohen_regular_complete`) and
  `Sheaf.TraceFormula.RegularSurfaceDepthOnePrincipal`
  (`RingTheory.regularSurfaceDepthOnePrincipal`). Both declarations and their
  proof docstrings were read; the proof plan refers to the recorded DAG nodes.

Edge cases checked before writing:

- `e = 0,1`: the unit ideal convention holds, and equality to the proper
  maximal ideal is impossible. No `e ≥ 2` hypothesis has been added.
- `s = 0`, or otherwise too few columns: the positive-size minor ideal is
  zero, as specified, not a unit ideal or a nonexistent minor.
- `H = 0`: when `e = 2` the power-series ring has depth two, so the depth-one
  assumption excludes it; it is not silently assumed nonzero.
- Arbitrary field universes are retained. The finite variable and generator
  index types impose no further size restriction.
- In characteristic two the discriminant is `b²`, and the linear derivative
  matrix has off-diagonal coefficient `b`; no inverse of two is used.
- Quadratic and linear parts are equalities of full homogeneous components.
  There is no assumption that `f` has no higher-order terms.

Searches for an existing statement (all rerun for this delivery):

- `msearch.py leanfinder`, query “A minimal formal power series quotient of
  depth one whose Jacobian minors generate the maximal ideal is a binary
  hypersurface with nonzero quadratic discriminant”: eight results, including
  standard smooth presentations, a minimal Weierstrass curve and standard
  étale pairs; none states this result.
- `msearch.py loogle`, query `MvPowerSeries.pderiv, Ideal.depth, Matrix.det`:
  zero hits.
- `msearch.py grep`, query
  `jacobian.*depth|Jacobian.*depth|quadratic.*hypersurface`: zero hits.
- `msearch.py leansearch`, query “A depth one minimal formal power series
  quotient whose Jacobian minors generate the maximal ideal is a plane
  hypersurface with nondegenerate quadratic term”: eight results on univariate
  Weierstrass preparation and the univariate maximal ideal, no match.
- `rg` in the project and upstream sources for the same expression and for
  `minimalJacobian|binaryHypersurface`: no matching statement; the only related
  hit was a proof-docstring reference in stable-modification field descent.
  `grep -rn` for the exact item id in `lean/WeilConjectures` returned no hit.
- Broader searches for `jacobian|Jacobian|minor` located the existing
  `Matrix.minorIdeal` and the later `formal_jacobian_quadratic_criterion`.
  The latter gives the completed quadratic model, not this statement about
  the original ideal and equation. Its composite helper definitions live
  in that downstream theorem's module. The present statement uses the
  existing general minor ideal directly, introducing no duplicate helper
  definition and no downstream import cycle.
- Mathlib source searches located `homogeneousComponent` and `pderiv`, both
  reused. The new theorem's full name was searched in Mathlib, upstream,
  project sources, and `dag/lean_names_upstream.json`, with no collision.

No new nodes, no dependency repairs, no statement correction. Only `lean` and
addition of the already landed `def-trf-minor-ideal` to `stmt_deps` are changed.
The dispatcher forbids subagents; the maintainer supplies independent review.

Validation: the module compiled cleanly through the prescribed server
`scompile.py` wrapper. The `deliver2.py --no-push` dry run reported that the
packet passes preflight and compiles, with precisely the item node, this
module, and this report staged. The expected `sorry` is the single named
theorem's whole proof.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
