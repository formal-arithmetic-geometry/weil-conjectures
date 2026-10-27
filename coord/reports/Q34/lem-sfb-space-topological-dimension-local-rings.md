## Worker report

States `AlgebraicGeometry.AlgebraicSpace.topologicalKrullDim_eq_iSup_etaleLocalRingDimension`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceTopologicalDimensionLocalRings`, with proof
`sorry`. The original natural-language statement and proof split are unchanged. The
only node changes are `lean` and the addition of the already landed statement dependency
`lem-sfb-space-local-dimension-chart-invariance` (brief-stage2 §5 permits landed nodes).
No new notion, auxiliary theorem, or dependency replacement is introduced.

Clause-by-clause correspondence:

- A scheme S: `{S : Scheme.{u}}`, for an explicitly declared universe `u`.
- An algebraic space X over S: `(X : AlgebraicSpace S)`, the recorded full subcategory
  of fppf sheaves with representable diagonal and a representable étale surjective atlas.
- Atlas topology: `Point X.obj.obj` has exactly the recorded `pointTopologicalSpace`
  instance from `AlgebraicSpacePointTopology`, not a topology chosen in this file.
- Quasi-separatedness as specified in this node: `hqs : IsRepresentableWith
  (fun _ _ p ↦ QuasiCompact p.left) (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj))`.
  The product of presheaves on `Over S` is the relative product over S. Its diagonal
  is tested against every scheme over S. `IsRepresentableWith` supplies an actual
  representing scheme projection, and Mathlib `QuasiCompact` requires the preimage
  of every quasi-compact open to be quasi-compact. This does not assume absolute
  quasi-separatedness of the base S.
- For each x, δ_X(x) is the *common chart stalk dimension*, not the infimum of
  dimensions of open neighbourhoods. It is rendered by
  `((etaleChart_localDimension X x).2.2.exists.choose : WithBot ℕ∞)`.
  The recorded theorem has conclusion `∃! d : ℕ∞, ...`: its first specification
  clause equates `ringKrullDim (W.left.presheaf.stalk w)` with the coercion of d for
  every representable étale chart and every w above x. Its other clauses guarantee
  chart existence, pairwise agreement, and agreement with scheme stalks. Thus
  `Exists.choose` selects a uniquely determined number. It is not data selected
  from a mere existence assertion, not an arbitrary chart, and not a new definition.
- Ring dimension and étaleness are exactly `ringKrullDim` and `IsEtale`, the latter
  defined by scheme base changes satisfying Mathlib `AlgebraicGeometry.Etale` in
  the imported chart-invariance theorem. Scheme local rings are its structure-sheaf
  stalks, as explicitly specified there.
- The equality is `topologicalKrullDim (Point X.obj.obj) = ⨆ x, ...`.
  Both sides live in `WithBot ℕ∞`, including negative infinity and positive infinity.
- No quasi-compactness of X, Noetherian, finite-dimensionality, equidimensionality,
  characteristic, nonemptiness, or separation hypothesis beyond hqs is present.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, and the recorded `IsEtale` interface.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace` and the existing point classes/point maps.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- Added landed node `lem-sfb-space-local-dimension-chart-invariance`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceLocalDimensionChartInvariance`,
  `AlgebraicSpace.etaleChart_localDimension`. Its full signature and proof docstring
  were read; the `∃!` clause provides exactly the local dimension used here.
- Plain proof imports: `AlgebraicSpaceJointSurjectivity.IsJointlySurjective`;
  `AlgebraicSpaceFibreProductPoint.exists_scheme_fibreProduct_point`;
  Mathlib `AlgebraicGeometry.Properties` (scheme sobriety); and
  `WeilConjectures.AlgebraicGeometry.Dimension`,
  `AlgebraicGeometry.Scheme.dim_eq_topologicalKrullDim`. The latter's `Scheme.dim`
  is explicitly the supremum of stalk Krull dimensions.

The proof nodes `lem-sfb-etale-stalk-invariants`,
`lem-sfb-quasiseparated-space-sober`, and
`lem-sfb-quasiseparated-space-etale-specializations` have no Lean record or Mathlib
match in the read snapshot. They are used only in the future proof, not to form the
statement; their modules are consequently not imported. Their roles are all preserved
in the five-step proof docstring. No unstated object is needed to type this delivery.

Edge cases checked before writing:

- Empty X: the point index is empty, so the supremum is bottom; Mathlib topological
  dimension is bottom too. No chosen value is evaluated at a nonexistent point.
- A field point: its chart stalk has dimension zero, so its uniquely selected number
  is zero; no shift, local-neighbourhood dimension, or positive-dimension bound occurs.
- A generic point of a positive-dimensional irreducible scheme: its local ring can
  have dimension zero while its neighbourhood dimension is positive. The selected
  number follows the stalk clause, so these distinct notions are not conflated.
- Unbounded dimensions and an infinite-dimensional stalk: `ℕ∞` admits infinity and
  `WithBot ℕ∞` admits arbitrary suprema; no maximum or finite witness is required.
- Non-quasi-compact spaces and non-quasi-separated bases: hqs is solely the relative
  diagonal condition on scheme tests, with no added global topological condition.
- Universe: all schemes and charts use the existing `Scheme.{u}`/`Over S` setup;
  `Point` remains in `Type (u+1)`, as in the recorded definition. No equality of
  independent universes or restrictive bound is imposed.

Searches for reuse (2026-10-24):

- `msearch.py leanfinder`, query "The topological dimension of a quasi separated
  algebraic space equals the supremum of the dimensions of its etale local rings":
  eight scheme quasi-separatedness, dimension and étale-site hits; no exact theorem.
- `msearch.py loogle`, query `topologicalKrullDim, ringKrullDim`: the sole hit is
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`, for affine spectra, not spaces.
- `msearch.py grep`, query `topologicalKrullDim|ringKrullDim`, subdirectory
  `AlgebraicGeometry`: nine hits, chiefly stalk/coheight and Artinian scheme lemmas.
- `msearch.py leansearch`, query "Dimension of the local ring at a point of an
  algebraic space computed in an etale scheme chart": eight ring/locally-ringed-space
  and scheme hits, including `IsLocalization.AtPrime.ringKrullDim_eq_height`; no
  algebraic-space common-value declaration in Mathlib.
- `msearch.py loogle`, query `"AlgebraicSpace"`: zero hits.
- `msearch.py grep`, query `etaleLocalRingDimension|etaleStalkDimension|localRingDim`:
  zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id and prospective
  theorem name: no existing item declaration. Searching space modules for
  `ringKrullDim.*stalk|stalk.*ringKrullDim` found the landed chart-invariance theorem,
  which is reused. Existing `AlgebraicSpaceEtaleDimension.etaleLocalDimension` uses
  `topologicalKrullDimAt` and is a different notion, so is not substituted.
- DAG search for `04NA` and "dimension of the local ring of" found chart invariance
  and related dimension-comparison consumers; no duplicate of this theorem.
  `blueprint_refs.py search dimension local ring` found 61 generic blueprint nodes;
  the relevant scheme dimension node is already a proof dependency. Search for
  `04NA` supplies no competing blueprint definition. `blueprint_refs.py ancestor`
  reports the inherited null ancestor; no new node is added.
- `rg` of the full prospective declaration name in Mathlib, both project roots,
  and `dag/lean_names_upstream.json` found no clash.

Sources opened: Stacks `spaces-properties.tex`, the complete statements and proof
of pre-dimension-local-ring / definition-dimension-local-ring / lemma-dimension
(Tags 0BAM, 04NA, 0BAN); `decent-spaces.tex`, lemma-bounded-fibres (03JX) and
lemma-dimension-decent-space (0A4J); and the current latest blueprint direct-images
proof (3). The source supports the unchanged statement. No statement dispute or
statement correction is needed.

Validation: scompile.py compiled the delivered module in both sandbox mode and its
library module name, without errors or unexpected warnings. `autoImplicit false`
is set, all universes and variables are explicit, and every source line is at most
100 characters. The sole postponed proof is the theorem named above.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
