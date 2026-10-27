## Worker report

The module `Sheaf.AlgebraicGeometry.FibrePurityFromHighDimensionImage` states
`AlgebraicGeometry.fibre_purity_from_high_dimension_image`. Its only theorem has
proof `by sorry`; the module introduces no definitions. The node is copied with
only `lean` changed. No new nodes, dependency repairs, or statement corrections
are needed, and no statement is disputed.

Sources read: `literature/stacks-project/limits.tex`, Tag 0EY2,
`lemma-descend-dimension-d`, especially the final image-containment argument;
`morphisms.tex`, Tag 02FY, `lemma-dimension-fibre-after-base-change`, part (1);
and `varieties.tex`, Tag 0B1B, `lemma-dimension-locally-algebraic`, the dimensions
of irreducible components through a point. Also read the current blueprint
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`
and its proof, to locate this subsidiary input without modifying the unit.

Hypothesis-by-hypothesis and clause-by-clause translation:

| Node text | Lean rendering |
| --- | --- |
| Schemes X, T, T' and f:X→T | `{X T T' : Scheme.{u}} (f : X ⟶ T)`; `u` is explicitly declared and arbitrary. |
| f is finite type | `[LocallyOfFiniteType f] [QuasiCompact f]`, the conjunction specified by the recorded finite-type node. |
| d is a nonnegative integer | `(d : ℕ)`; dimension comparisons use `(d : WithBot ℕ∞)`. |
| Every scheme-theoretic fibre has dimension ≤ d | `hupper : ∀ t : T, topologicalKrullDim (f.fiber t) ≤ (d : WithBot ℕ∞)`. |
| E consists of x with local fibre dimension ≥ d | The literal set `{x : X \| (d : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.asFiber x)}` in `himage`. |
| Any morphism g:T'→T | `(g : T' ⟶ T)` with no typeclass assumptions on g. |
| X'=X×_T T' and its projections p, f' | Mathlib's chosen `pullback f g`, `pullback.fst f g`, and `pullback.snd f g`. |
| p(|X'|)⊆E | `himage : Set.range (pullback.fst f g) ⊆` the preceding literal set. |
| For every x', dim at x' in its f'-fibre equals dim at p(x') in its f-fibre | The first conjunct under `∀ x' : ↥(pullback f g)` equates `topologicalKrullDimAt ((pullback.snd f g).asFiber x')` and `topologicalKrullDimAt (f.asFiber (pullback.fst f g x'))`. |
| Both displayed local dimensions equal d | The second conjunct under the same quantifier sets the latter dimension equal to `(d : WithBot ℕ∞)`; together these render the chained equality exactly. |
| Every nonempty fibre of f' is pure of dimension d | `∀ t' : T', Nonempty ((pullback.snd f g).fiber t') → ((pullback.snd f g).fiber t').IsPureDimension d`. |
| In particular every irreducible component has dimension d | This is the definition of `Scheme.IsPureDimension`, namely `∀ Z : Set X, Z ∈ irreducibleComponents X → topologicalKrullDim Z = (d : WithBot ℕ∞)`. There is no weaker substitute for purity. |
| Empty source and empty fibres allowed | No `Nonempty` assumption on X, T, T', or the pullback. Empty fibres satisfy `hupper` because their dimension is bottom; the purity conclusion has exactly the node's nonempty-fibre antecedent. |
| No lfp, flatness, separatedness, properness, or finite type required of g | No such binders or instances occur. |

The canonical `Scheme.Hom.asFiber` puts each ambient point into the
scheme-theoretic fibre over its image; it does not use the local ring dimension.
Thus the two terms compare the node's local topological dimensions, in exactly
the specified fibres. No `let` binders, auto-bound variables, local notation,
private definitions, or noncanonical choices occur in the signature.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, declaration
  `AlgebraicGeometry.LocallyOfFiniteType`, together with
  `AlgebraicGeometry.QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (publicly available through
  FiniteType). These are exactly the recorded finite-type conjunction.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`, declarations
  `AlgebraicGeometry.Scheme.Hom.fiber`, `fiberι`, and
  `fiberToSpecResidueField`. The same module supplies `asFiber`, read together
  with `fiberHomeo` and `fiberι_asFiber`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, declarations
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd`.
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`, declaration
  `AlgebraicGeometry.Scheme.IsPureDimension`. Its definition tests the subspace
  topological Krull dimension of every irreducible component, including the
  vacuous empty-space case.
- `def-kun-topological-dimension-at-point`:
  `WeilConjectures.Mathlib.Topology.KrullDimension`, declaration
  `topologicalKrullDimAt`, the infimum of dimensions of open neighbourhoods.
- `def-kun-topological-krull-dimension`:
  `Mathlib.Topology.KrullDimension`, declaration `topologicalKrullDim`.

The statement-dependency modules are public imports. The stated proof dependency
`lem-sc-fibre-dimension-after-base-change` is imported privately as
`Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`; its declaration
`AlgebraicGeometry.fibre_dimension_after_base_change` and docstring were read.
The Mathlib proof leaf `lem-weil-pbc-lft-base-change` is already available from
FiniteType as `AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange`
and its instances for the two projections. The proof-only node
`lem-trf-field-extension-component-local-dimension` currently has no Lean
record or Mathlib match, so it has no module to import; its stated argument is
included explicitly in the theorem docstring. It is not needed to type this
statement and is not duplicated here.

Edge cases checked before writing:

- Empty X or empty T': there are no pullback points, and no nonempty fibres to
  which the last clause applies. No inhabitance was introduced.
- Empty fibre over t: `topologicalKrullDim` is bottom, so the upper bound allows
  it for every d; no dimension of an artificial point is requested.
- d=0: nonempty zero-dimensional fibres meet the sandwich at zero, and every
  irreducible component has dimension zero.
- Identity base change: `himage` requires every point of X to lie in E and the
  result says each fibre has constant local dimension d and is pure d.
- X equal to the disjoint union of an affine line and a point over a field,
  d=1: the isolated point has local dimension zero and fails the image condition
  for an identity base change. Thus the criterion does not incorrectly make this
  mixed-dimensional fibre pure one-dimensional.
- A plane and a line meeting in a point: the generic point of the line has local
  dimension one; d=2 excludes it from E. The condition tests all image points,
  rather than only closed points or intersections.
- Arbitrary inseparable, transcendental, or non-finite-type base change is allowed:
  the only conditions are on f, its fibres, and the image of the projection.

Searches for an exact existing statement (2026-10-24):

- `msearch.py`, LeanFinder query: "A finite type scheme morphism with fibre
  dimensions bounded above by d has pure d dimensional fibres after any base
  change whose image has local fibre dimension at least d". Eight hits concern
  stability of finite type, finite morphisms, smooth relative dimension,
  preimmersions, and quasi-finiteness; none has this image criterion.
- `msearch.py`, Loogle query: `"topologicalKrullDim"`. Seven hits:
  `topologicalKrullDim`, homeomorphism invariance, the discrete-topology bound,
  inducing-map and subspace inequalities, prime-spectrum/ring dimension equality,
  and the locally Artinian criterion. None is the statement.
- `msearch.py`, Mathlib grep query:
  `equidimensional|[Pp]ureDimension|[Dd]imension.*[Ff]iber|[Ff]iber.*[Dd]imension`,
  subdirectory `AlgebraicGeometry`. One hit in
  `AlgebraicCycle/Basic.lean:65`, an explanatory comment that equidimensionality
  hypotheses cannot be assumed. No match.
- `msearch.py`, LeanSearch query: "A finite type morphism with fibres of
  dimension at most d has pure dimension d fibres after base change when the
  image is in the locus of local fibre dimension at least d". Eight hits give
  smooth relative-dimension stability, finite fibre cardinality, and finite,
  etale or proper base-change facts. None is the statement.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for
  `fibre.*pur|fiber.*pur|high.*[Dd]imension|purity_from` found related purity,
  relative-dimension and higher-direct-image statements. Read
  `RelativeDimensionBaseChange.lean`: its theorem assumes existing pure fibres,
  whereas this item deduces purity from an upper bound and an image condition.
  Read `EquidimensionalFibreOpenPartition.lean`: it defines constant local
  fibre-dimension open pieces in a different setting; it does not state this
  criterion.
- `grep -rn` of the item id in `lean/WeilConjectures` found no attachment.
  `rg` of the item id, proposed theorem name, and proposed module name in
  `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf` found
  no declaration or collision.

Validation: `scompile.py Q11 lem-trf-fibre-purity-from-high-dimension-image`
compiled the delivered module against the current server sources in 1.5 seconds,
exit 0, with no Lean errors or unexpected warnings. The wrapper first reported
an unavailable cached compile due to lack of device space, then automatically
confirmed successfully against current server sources. All source lines are at
most 100 characters; every variable and universe is explicitly bound.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
