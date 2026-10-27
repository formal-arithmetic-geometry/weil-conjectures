## Worker report

The module `Sheaf.AlgebraicGeometry.FormalHilbertStratumMinors` states every clause of
`lem-trf-formal-hilbert-stratum-minors` in four theorems. All four proofs are `sorry`;
all eleven helper definitions have real data. The helpers are the explicit matrices,
ranks and ideals introduced by this node, including an adapter from finite index types
to the recorded `Matrix.minorIdeal`. No separate independent notion is introduced.

Source read: ILO VIII 2.3.11 and 2.3.13, printed pp.93--94 (PDF pp.99--100), in the
repository; Bierstone--Milman, Invent. Math. 128 (1997), (7.1)--(7.2), Definitions
7.9--7.13, Theorem 7.14, and Remarks 9.1 and 9.5, in the journal PDF at
https://mahalex.net/teaching/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf
(read with the web tool). The ILO source supplies the route, not the matrix computation.
The theorem docstrings carry the node's thirteen proof steps, divided among the four
clauses. No source or node correction is needed.

Hypotheses and conclusions of the formal theorem:

- The characteristic-zero field is `{L : Type u} [Field L] [CharZero L]`.
  `m,n,s : ℕ` count W variables, Z variables, and vertices; all may be zero.
  `MvPowerSeries (Fin m ⊕ Fin n) L` is exactly A=L[[W,Z]], and `K : Ideal ...`
  is the given ideal, without an added finiteness assumption.
- `α : Fin s → Fin n →₀ ℕ` describes the transverse vertices. `fullVertex m`
  inserts zero W components. `hdegree` orders their degrees nondecreasingly;
  `hminimal` makes them distinct minimal vertices; `hessential` says every Z
  variable occurs. The diagram is the union of their orthants, using the existing
  `inDiagram`; `inDelta` assigns each exponent to its first vertex.
- `horder` states separately that every f_i lies in K and has order |α_i|.
  `hdivision : homogeneousDivision α f` is the existing unique supported
  homogeneous division predicate, for every degree and every degree prefix.
- `hgeneration` gives every element of K as a supported sum of the f_i.
  The reverse inclusion is supplied by `horder` and ideal closure, so this is the
  asserted equality of K with those sums, not merely unrestricted generation.
- Blocks are indexed by a degree b that actually occurs. Nondecreasing vertex
  degrees identify its prefix with indices up to s_ell. The subtype
  `{j : Fin n // essential α b j}` is precisely Z^ell.
- `hblocks` chooses pick and β for each accumulated block, with
  `α (pick j) = β j + single j 1`, prefix membership, membership of the selected
  derivative in `transverseIdeal α b`, and a unit constant Jacobian determinant
  on exactly those essential variables. Choices may depend on the block, as in
  the node. No single compatible global choice is imposed.
- `hlater` quantifies over every later generator and every δ of degree at most Q
  supported on the accumulated essential variables, lying in the prefix diagram;
  its derivative belongs to the prefix variable ideal. This is the restricted
  orthant-diagram condition, including all remaining W and Z coefficients.
- `hQ` and `hq` use `((α i).degree : ℤ) - 1`, with no natural-number subtraction.
  For a nonempty list, the pointwise bounds equal the max-degree-minus-one bound.
  For an empty list every natural Q,q is allowed, agreeing with max empty = 0.
- `formalJetMatrix f t` has rows δ and columns (i,η), both monomial indices of
  degree at most t. The entry is zero unless η≤δ, and otherwise is
  (δ-η)! inverse times the (δ-η)-derivative of f_i. Thus these are exactly the
  coefficients of Y^η f_i(X+Y) modulo (Y)^(t+1), with no formal-substitution
  witness or arbitrary linear map assumed.
- `formalJetRank` specializes this matrix using `MvPowerSeries.constantCoeff`
  and takes its rank over L. `formalJetMinorIdeal` calls the recorded minor
  ideal at this rank plus one. `formalStratumIdeal` is the supremum (ideal sum)
  over t in range(q+1), including t=0. `lowDerivativeIdeal` spans all derivatives
  with total order strictly below |α_i|. Their equality is the main conclusion.

Further clauses:

- `formalJetMinorIdeal_generator_independent` quantifies over any two finite
  generator families with equal ideal spans, and any t. It imposes none of the
  division or block hypotheses, since independence only uses the ideal K.
- `regularJetMinorIdeal_map_taylor` uses an affine chart U, its structure
  morphism p over a characteristic-zero field k, and `[Smooth p]`,
  `[LocallyOfFiniteType p]`, `[QuasiCompact p]` for smooth finite type.
  `c.Etale` supplies the coordinate chart, and `hover` pins its k-structure to p.
  `D` are regular coordinate derivations: `hDk` kills the base field and `hDx`
  gives the Kronecker delta on coordinates. They are written as ℤ-derivations
  to avoid introducing a second algebra structure on Γ(U,top); these equations
  specify the canonical k-coordinate derivations, uniquely by étaleness.
  `T b` are the existing Taylor maps, pinned by `isTaylorMap` on scalars,
  coordinates and residue values. The node already supplies these notions;
  the quantified maps are characterized, not arbitrary maps.
  `regularJetMatrix` is the same factorial-derivative formula with regular
  functions and their coordinate derivatives. Its rank in `regularJetMinorIdeal`
  is evaluated in the residue field of the distinguished point a and then frozen.
  The theorem states its ideal maps under T_a exactly to the formal minors
  of the Taylor expansions of the regular generators. Arbitrary finite h are
  allowed, and they define their closed subscheme by `Ideal.span (Set.range h)`.
- `regularStratum_zeroLocus_germ` uses the same chart and canonical coordinate
  and Taylor data. `hfinite` is finiteness of the set of full sequence values
  on some open containing a, rather than coordinatewise finiteness.
  Its conclusion gives q₀ and, for every q≥q₀, an open neighbourhood V of a
  on which the ideal sum is contained in the kernel of evaluation at b iff
  the full extended Hilbert functions at b and a are equal. This is precisely
  equality of the underlying set germs, not an assertion of equality of scheme
  structures. Enlarging q₀ also accommodates any prescribed vertex-degree bound.
  `extendedHilbert` and `taylorIdeal` retain all d relative coordinates at
  nonclosed points and use the residue field of each point individually. Their
  module-length convention equals the finite residue-field dimension here.
  There is no closed-point hypothesis, residue-field identification or restriction
  to a dense/open equality locus. Passing to an affine coordinate neighbourhood
  is the ordinary local chart convention and loses no germ.

Dependency declarations read and used:

- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, its ring/algebra
  operations and coefficient access, matching the recorded power-series node.
- `Mathlib.RingTheory.MvPowerSeries.Derivative`: `MvPowerSeries.pderiv` and its
  coefficient formula, matching the dependency's `mathlib_match` (no `lean`
  record is needed for that leaf).
- `Sheaf.LinearAlgebra.Matrix.MinorIdeal`: `Matrix.minorIdeal`, the exact
  increasing-row/column finite-matrix definition; no second minor definition.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` giving finite type as recorded by the dependency node.
- Added the already landed `def-trf-regular-hilbert-coefficient-datum` to
  `stmt_deps` to reuse `AlgebraicGeometry.HilbertCoefficient.fullVertex`,
  `inDiagram`, `inDelta`, `essential`, `supported`, `transverseIdeal`,
  `iteratedPartial`, `homogeneousDivision`, `isTaylorMap`, `taylorIdeal`, and
  `extendedHilbert`, from `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum`.
  Its stronger `orderedVertices` and bundled `formalConditions` are deliberately
  not assumed: this node allows any tie order and per-block choices.
- The stated proof dependency `Sheaf.RingTheory.PresentationFittingIdeal` is
  imported non-publicly; read `LinearMap.presentationFittingIdeal` and the full
  `presentationFittingIdeal_independence_baseChange` signature/docstring.
  `lem-trf-implicit-taylor-coordinate-calculus` and
  `lem-trf-jet-diagram-hilbert-control` have no recorded modules in this base;
  they are proof dependencies only, and are named in the proof plans without
  inventing interfaces or making this delivery depend on their statements.

Edge cases checked mathematically before writing and during the second reading:

- s=0 forces K=0 from supported generation. The matrices have no columns, rank 0,
  and the 1-minors ideal is zero. The derivative span is empty and zero.
- A degree-zero vertex forces the only minimal vertex to be 0, all Z variables
  absent, and its generator to be a unit. The matrix has full row rank; minors
  one larger than this rank vanish. No derivative has degree <0.
- m=0, n=0 and d=0 are allowed. There is always the constant monomial; an empty
  essential block has determinant 1. No nonempty subtype instance is assumed.
- t=0 includes the original generators as the unique unshifted columns; q=0 is
  permitted exactly by the integer bounds. q may exceed Q: the conclusion makes
  no accidental upper bound on q.
- Rank zero uses 1-minors and rank equal to the row count uses oversized minors;
  there is no negative Fitting index or accidental unit ideal from 0-minors.
- For f=z²+w³ at the origin, the hypotheses hold for the one-vertex diagram
  (0,2); q=1 gives the ideal (z,w²) on both sides.
- At a nonclosed point the Taylor ring keeps every relative coordinate. The germ
  equality compares the extended functions, not ordinary local lengths with a
  varying dimension shift omitted. Points outside the closed subscheme have the
  zero function, and are not excluded.

Searches actually run via the prescribed msearch wrapper (logged in searches.jsonl):

- LeanFinder, `formal standard basis derivative equimultiplicity ideal equals
  cumulative determinantal ideals of truncated Taylor modules`: eight hits on
  different ideals, submersive presentations, Weierstrass series and Smith
  coefficients; none is the comparison theorem.
- Loogle, `MvPowerSeries.pderiv, Matrix.det`: zero hits.
- LeanSearch, `formal standard basis derivative ideal cumulative minors Taylor
  matrices Hilbert Samuel equality locus`: eight hits on polynomial sequences,
  Kähler bases and submersive Jacobians; none states this result.
- Mathlib grep, `Taylor|Hilbert.?Samuel|equimultiple|stratum.*minor`, RingTheory:
  17 hits, involving univariate polynomial Taylor operations; no formal stratum.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for Taylor/Hilbert/orthant and
  iteratedPartial/homogeneousDivision/jetMatrix/taylorMatrix/jetMinor/TaylorMap
  found the landed coefficient-datum definitions reused above and no theorem
  matching this node. The exact node-id grep of `lean/WeilConjectures` was empty.
- `rg` of Mathlib, both project source trees, and `dag/lean_names_upstream.json`
  for the helper and theorem names found no collisions. The DAG search for
  Taylor/Hilbert definitions found the existing coefficient-datum node, so no
  duplicate node was created.

Validation: prescribed scompile.py compiled both its sandbox and the actual module
cleanly (3.6 s and 5.0 s). The first compile diagnosed function-field rank syntax and
an open-Classical linter warning; repaired with explicit `Matrix.rank` and scoped
`open Classical in`. All variables and universes are explicit, autoImplicit is false,
all lines are at most 100 columns, and no diagnostic commands remain.

## Second reading by Q06

A separate rereading matched the node, the dependency definitions, and the completed
Lean file clause by clause. No second agent was started, following the dispatcher
instruction; the maintainer supplies the independent review. The checks above record
this worker's second reading rather than claiming an independent worker review.

The rereading specifically rejected using `orderedVertices` (it would impose a tie
order absent from this node) and the bundled `formalConditions` with a single global
pick (the node permits choices in each block). The final theorem instead has
`hdegree`, `hminimal`, and the per-block existential `hblocks`. Integer bounds,
all t=0..q, all matrix monomial multiples, generator independence, Taylor compatibility,
and the full sequence germ were checked against the node. The finite-value condition
was checked to be finiteness of entire functions. Canonical derivations and Taylor
maps are fixed by their coordinate/scalar/residue characterizations, so no arbitrary
map or unrelated formal ideal enters the chart assertions. No mismatch remains.
