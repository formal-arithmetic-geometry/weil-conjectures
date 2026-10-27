## Worker report

The delivery states Stacks Tag 04T7 as
`AlgebraicGeometry.Scheme.cardinalSize_le_of_locallyOfFiniteType` in
`Sheaf.AlgebraicGeometry.QuasiCompactLocallyFiniteTypeSchemeSize`. Its proof is `sorry`.
The accepted stage-1 statement and four proof steps are unchanged. The module docstring
records all four steps and their dependencies for stage 3.

Hypothesis and clause correspondence:

- The schemes X and S are `{X S : Scheme.{u}}`, with arbitrary explicit universe `u`.
  `f : X ⟶ S` is their given morphism, not a replacement structure morphism.
- Local finite type is `[LocallyOfFiniteType f]`, using the dependency's recorded class.
- Quasi-compactness of X is `[CompactSpace X]`, without a separation condition.
- The inline size invariant is `Scheme.cardinalSize`. For any scheme Z,
  `Z.affineOpens` is the subtype of its open subsets satisfying `IsAffineOpen`;
  `Cardinal.mk Z.affineOpens` counts that set, including the empty affine open.
  `Γ(Z, U.1)` is the structure sheaf's ring of sections on the actual open subset U.
  `⨆ U : Z.affineOpens, Cardinal.mk ↥Γ(Z, U.1)` is the specified supremum of cardinalities
  of section rings. The outer `max Cardinal.aleph0` and inner `max` are exactly the
  three-term maximum in the node. All these cardinals and indexing types live in `u`.
- The conclusion is `X.cardinalSize ≤ S.cardinalSize`.
- There is no quasi-compactness or quasi-separatedness assumption on S, no
  quasi-separatedness assumption on X, and no quasi-compactness assumption on f.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and the scoped `Γ(X, U)` notation for the structure sheaf sections.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, the all-affine-pairs finite-type condition
  recorded by def-weil-finite-type-morphism. Its module docstring also explains that
  finite type would require quasi-compactness; that extra property is not used here.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, as recorded on
  def-weil-pbc-quasi-compact-scheme. Its docstring explicitly excludes a separation axiom.
- The new definition module publicly imports `Mathlib.AlgebraicGeometry.AffineScheme`
  for `Scheme.affineOpens`, whose full definition is `{U : X.Opens | IsAffineOpen U}`.
- The stated proof inputs are available via these imports and the ordinary proof import
  `Mathlib.SetTheory.Cardinal.Arithmetic`, containing `Cardinal.mk_list_le_max`.
  `Scheme.isBasis_affineOpens` is in AffineScheme and `Spec` in Scheme.
  The proof nodes lem-sfb-affine-scheme-size and lem-sfb-open-cover-scheme-size currently
  have no Lean bindings and therefore have no proof-module imports yet.

Source and edge checks: read sets.tex's definition before Tag 000I and the entire
lemma-bound-finite-type (04T7), which has exactly these assumptions. For the empty scheme
the affine-open set has one element and its section ring is the zero ring, so size is
aleph zero. An empty finite chart family is allowed. For Spec of a finite field, size is
aleph zero. For an uncountable affine coordinate ring the invariant retains its actual
cardinality, rather than counting only points or a chosen cover. Zero algebra generators
and the zero algebra are covered by the documented polynomial-expression argument.
Identity morphisms give equality for quasi-compact X. An open affine chart in a
non-quasi-separated scheme is an example for which the morphism need not be quasi-compact;
the binders impose no such property. No noetherian, separated, nonempty, or finite-field
restriction is introduced. The universe is explicitly bound and autoImplicit is false.

Searches executed with msearch.py for this assignment:

- LeanFinder: “The size of a scheme is the maximum of aleph zero, the cardinality of
  affine opens and the supremum of the cardinalities of their rings of sections;
  quasi compact locally finite type schemes have size bounded by the base”. Eight
  results concern compactness, affine opens, quasi-affineness and finite type; none is
  the size definition or theorem.
- Loogle: `"LocallyOfFiniteType", "Cardinal"`: no results.
- LeanSearch: “Cardinal size of a scheme maximum countable affine opens sections”:
  eight results give affine opens/covers and unrelated structural SizeOf declarations.
- Mathlib grep: `(schemeSize|scheme_size|cardinalSize|size.*[Ss]cheme|[Ss]cheme.*size)`
  in AlgebraicGeometry: only Modules/Tilde's preservation-of-colimits size parameter.
- Separate LeanSearch for the full definition, Loogle `"affineOpens", "Cardinal"`, and
  the corresponding Mathlib grep were executed and their raw result records are in the
  new definition node's mathlib_searches. None gives this definition.
- rg in WeilConjectures and Sheaf for schemeSize, scheme_size and cardinalSize: no
  declaration. The broader scheme/size search finds coefficient/site-universe discussions
  and unrelated finite chart sizes. Search for the item id in WeilConjectures: no hit.
- Searched definition nodes for “size of a scheme”, “scheme size” and the displayed
  size formulas: no definition node. The nearby affine-size, open-cover-size and bounded
  big-site nodes are statements, not definitions. blueprint_refs.py search “scheme size”
  returns zero blueprint nodes.

No statement correction, disputed statement, or dependency-interface repair is needed.
The inherited BLOCKED ending concerned a stage-1 re-split; brief-stage2 section 0 permits
this stage-2 formalization because the accepted node has no Lean record.

Both delivered modules compiled cleanly through scompile.py, individually and in dependency
order, against the live published library. No local or global build was run.

## New nodes

def-sfb-scheme-cardinal-size defines exactly the inline size invariant used in the item,
from sets.tex section-categories-schemes preceding Tag 000I. Its real-data definition is
`AlgebraicGeometry.Scheme.cardinalSize` in `Sheaf.AlgebraicGeometry.SchemeCardinalSize`.
There is no sorry in the definition. It uses the existing scheme, affine-open and section
ring constructions, rather than copying them. Its searches are recorded as actual
msearch.py results; DAG and project searches are described above. The item gains this
definition in stmt_deps. The ancestor search returns null, as in the item's inherited
blueprint.from.node, and the via chain is extended by the item id.

## Second reading by Q103

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
