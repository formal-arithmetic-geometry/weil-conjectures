## Worker report

The module Sheaf.AlgebraicGeometry.ProperSpaceFibreDimensionUpperSemicontinuous supplies
fibreDimensionOverScheme and the sorry-only theorem proper_fibreDimension_finite_isOpen.
There is no statement correction and no new or repaired dependency node.

Clause-by-clause correspondence:

- The target scheme is `T.left`, for `T : Over S`. The ambient scheme S only records
  a common base for the existing algebraic-space category. Every scheme target in
  the node is covered by taking S equal to that target and T the identity over S.
  No separatedness or finiteness is required of T or S.
- The source is the actual `X : AlgebraicSpace S`; its morphism to T is
  `f : X ⟶ schemeSpace T`. This retains algebraic-space sources, rather than
  replacing them by schemes, and uses the published representable sheaf of T.
- `t : T.left` ranges over all target points. The helper's pullback is formed from
  `f.hom.hom` and the Yoneda map of `T.left.fromSpecResidueField t`, with its
  composite to S. Thus it is exactly X ×_T Spec κ(t), retaining the canonical
  residue-field map, not a chosen geometric point or a supplied arbitrary fibre.
- Its dimension is the published `etaleDimension` of that presheaf fibre. This is
  the same dimension as the node's affine-chart supremum: expand etaleDimension
  into the supremum over points, charts and chart points; refine each scheme chart
  by affine opens. The dimension of each chart is the supremum of its local
  topological dimensions, so reindexing these suprema gives precisely the supremum
  of Krull dimensions of affine representable etale charts. Conversely each such
  affine chart contributes its local dimensions to the expanded supremum. No new
  global dimension predicate is defined. The empty fibre has no chart points, so
  this supremum is bottom, meaning −∞, also with the empty affine chart permitted.
- `hf : MapIsProper f` is exactly separated, finite type, universally closed.
  Its published definition expands into MapIsSeparated f, MapIsFiniteType f,
  MapIsUniversallyClosed f. These are respectively closed-immersion scheme tests
  of the representable diagonal; quasi-compactness plus local finite type on
  compatible etale charts; and IsClosedMap on point classes after every
  algebraic-space base change. Point classes carry the published atlas topology.
  The scheme morphism predicates used inside the chart tests are the recorded
  Mathlib LocallyOfFiniteType and IsClosedImmersion, with no private replacements.
- The first conjunct `∀ t, ... = ⊥ ∨ ∃ n : ℕ, ... = (n : WithBot ℕ∞)` says exactly
  that each value lies in {−∞,0,1,...}, excluding +∞.
- The second conjunct quantifies `a : ℤ` with `-1 ≤ a`. The displayed conditional
  threshold is bottom for a = −1 and the coercion of a.toNat for a ≥ 0. There are
  no other negative cases in this quantifier. IsOpen states openness of {n_f ≤ a};
  IsClosed states closedness of the order-complement {a < n_f}, explicitly rendering
  both equivalent forms in the node. No monotonicity, uniform dimension bound,
  flatness, finite presentation, or Noetherian assumption is added.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom, Spec, Spec.map.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  IsRepresentableWith, IsEtale and the actual underlying fppf sheaves.
- Mathlib.AlgebraicGeometry.ResidueField: Scheme.residueField,
  Scheme.fromSpecResidueField. Their full definitions use the stalk quotient and
  canonical Spec map.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, etaleCover_pullback, etale_fibreProduct_isScheme.
  These justify treating the sheaf pullback as the algebraic-space fibre. The
  construction uses the actual Limits.pullback, without choosing a representing space.
- Mathlib.Topology.KrullDimension: topologicalKrullDim, used by the existing
  local/topological dimension infrastructure.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper, IsSeparated,
  UniversallyClosed, read as the scheme conventions inside the recorded space API.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: pointTopologicalSpace,
  pointImage, PointRepresentative.map.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsProper and its
  MapIsSeparated, MapIsFiniteType, MapIsUniversallyClosed constituents. Its definition
  owner def-sfb-space-morphism-properties is added to stmt_deps.
- Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite: schemeSpace, with its declaration
  owner def-trf-scheme-algebraic-space added to stmt_deps.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleDimension: etaleDimension and
  etaleLocalDimension; owner def-sfb-algebraic-space-etale-dimension added to stmt_deps.
- The stated proof dependency AlgebraicSpaceLocalFibreDimensionOpen is a plain
  import. I read localFibreDimension and localFibreDimension_chart_finite_isOpen
  in full. The other proof dependency lem-sfb-space-fibre-dimension-supremum has
  no Lean record or Mathlib match in the read clone, so has no module to import;
  it is not needed to type the present statement. Its mathematical proof input is
  preserved in the docstring and DAG without a new proof obligation or a cycle.

Sources checked: literature/stacks-project/spaces-more-morphisms.tex,
lemma-dimension-fibre (0D4M), lemma-dimension-fibres-proper (0D4Q), including their
proofs. The proof docstring follows all four steps in the node, including a = −1.
The prescribed CompactObject example has been withdrawn; its node now points to
WeilConjectures.CategoryTheory.CompactObject. I followed the live module conventions.
No repair note exists for this item.

Edge cases checked before writing: empty source (all dimensions bottom; every
allowed sublevel is the whole target and its complement empty), empty target
(all point assertions vacuous), identity of a scheme (dimension zero everywhere),
proper closed immersion (dimensions zero or bottom), positive-dimensional proper
fibres (a = −1 correctly excludes every nonempty fibre), dimension-zero fibres
(a = 0 includes them), disjoint components of different dimensions (no purity
assertion), arbitrary non-Noetherian target and arbitrary characteristic.
The codomain still allows +∞ in the construction; its exclusion is a theorem
conclusion, not an assumption. The universe u is explicit and autoImplicit is false.

Searches for an existing statement, all via the prescribed tools:

- msearch.py leanfinder, query "For a proper morphism of algebraic spaces fibre
  dimension is upper semicontinuous": eight results, all scheme properness or
  scheme underlying-map lemmas, none the algebraic-space statement.
- msearch.py leansearch, same query: eight results, general UpperSemicontinuous
  definitions and scheme properness, no matching theorem.
- msearch.py loogle, query `"UpperSemicontinuous", "AlgebraicGeometry"`: zero hits.
- msearch.py grep, query
  `upperSemicontinuous.*dim|dim.*upperSemicontinuous|proper.*[Ff]ib.*[Dd]im`:
  one unrelated elliptic-curve documentation hit.
- rg in lean/WeilConjectures for the item id: no hit. Names file search for
  fibreDimension/fiberDimension found only finite locally free degree statements.
- rg in lean/Sheaf and lean/WeilConjectures for proper fibre dimension,
  upperSemicontinuous, fibreDimensionOverScheme and proper_fibreDimension:
  the scheme theorem ProperFibreDimensionUpperSemicontinuous has scheme source
  and natural thresholds; it does not cover this node. Upstream semicontinuity
  for coherent cohomology concerns vector-space ranks. Neither is reused as an
  existing match. Concept searches located the three definition owners used above.

No STATEMENT-DISPUTED flag or node fault was found. All definitions have real data.

## Second reading by NL

Self-reread in this dispatcher-started worker; no second agent was started, as the
brief forbids it. The maintainer performs the independent review.

I compared the node with the completed file: actual algebraic-space X, actual
scheme target T.left, morphism f, canonical residue field fibre, the already defined
chart dimension, properness in all three constituents, finiteness including bottom,
all integer thresholds ≥ −1, and both open/closed versions are present. The scheme
encoding introduces only a common ambient base, not an additional geometric
hypothesis: S may be the target with its identity structure map. I expanded the
recorded dimension definition to verify its equality with the affine-chart supremum,
including the empty case. I also checked the direction of the pullback and the
order comparison in the closed locus. The conditional threshold agrees with the
integer cut exactly on the quantified range. The stated local-dimension proof
input is a non-public import; no unavailable proof input is falsely claimed to
have a module. No mismatch or statement correction resulted from this reread.
