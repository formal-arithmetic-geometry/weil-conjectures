## Worker report

The module `Sheaf.AlgebraicGeometry.NormalizedResolutionWordGluing` states
`AlgebraicGeometry.EmbeddedResolutionHistory.normalized_resolution_word_gluing`, with
`sorry` as its only proof. Its helpers spell out the local word prescription and have
actual data. No definition selects data from a postponed existence result. The node's
natural-language statement is unchanged. Its statement dependencies gain
`def-trf-chronological-history-boundary`, which owns the already landed plain definition
`coefficientHistoryBoundary`. The comparison theorem remains a proof dependency; its
conclusions are not needed to construct the boundary or state the chart interface.

The clause-by-clause correspondence is as follows.

- Rational embedded inputs: `EmbeddedResolutionPair.{u}` supplies `X`, `P`, `base`,
  `inclusion`, `closed`, `reduced`, `smooth`, `separated`, `finiteType`, and
  `quasiCompact`. Its base is `Spec (.of (ULift.{u} ℚ))`; no connectedness,
  equidimensionality, nonemptiness or dimension bound is imposed.
- The fixed simultaneous marked-ideal assignment is the binder
  `R : MarkedIdeal.NumericalResolution.{u}`. Its `value` is used literally in
  `ResolutionWordChart.tail`; no independent numerical labelling is substituted.
- Local lengths, minimum component dimension and number of distinct component dimensions
  are exactly `HilbertSamuel.localFunction`, `minimumComponentDimension`, and
  `componentDimensionCount`. `HilbertSamuel.normalizedHead H.X x` is their existing
  pair `(c, Δ^q h)` with integer-valued finite differences. Thus these definitions are
  reused rather than copied.
- The fixed common value space is
  `HilbertSamuel.ResolutionWord := WithBot (DimensionHead ×ₗ MarkedIdeal.Word)`.
  It has the lexicographic head, lexicographic finite engine tail, and a new bottom.
  It has no `D` or scheme parameter.
- At singular points, `ResolutionWordChart.singular`, `minimal`, `presents`, `level`
  and `maximal` specify a full-envelope maximal-order presentation in a minimal
  envelope. `freshWordEmbedded` replaces only the test boundary by `[]`, and
  `freshWordMarked` retains the same ideal, marking and support. Thus the new tests
  start empty without erasing the numerical input's recorded exceptional history.
- `wordEarlierCenters` extends the actual intrinsic center ideals chronologically;
  `ResolutionWordChart.earlierPullback` identifies them with the local recorded ideals.
  `boundary` uses the existing `coefficientHistoryBoundary`, retaining schematic strict
  transforms and actual appended birth ideals. `births` relates the numerical history's
  relative birth times to their positions in the full chronological history. Older
  components have relative birth zero when a new presentation is chosen, with their
  original order and absolute positions retained by the full boundary and earlier list.
- Controlled transforms at transformed stages are the actual
  `MarkedIdeal.History.step` data. These use `Step.Transforms` with the marking-th
  exceptional-power equation and scheme-theoretic strict transforms. The chart's
  `intrinsic`, `transitionSquare`, `naturality`, `centers`, `centerSource` and
  `centerTarget` identify the suffix with the actual embedded-history stages and their
  center ideals. This is not an arbitrary map between unrelated transformed schemes.
  The suffix begins when the current head is first attained (`firstHead`) and retains
  it (`retainedHead`). A vanished old cosupport is not used after a head drop.
- The explicit normalization conjunct asserts that the engine word has leading
  `MarkedIdeal.rational 1`. `tail` then applies `.drop 1`. `maximalStages` uses the
  existing maximal-order predicate on the numerical representatives throughout that
  retained-head suffix.
- Existence of local prescriptions is the `Nonempty (ResolutionWordChart R H x)`
  conjunct at every singular point. This is a theorem conclusion, not an assumed
  choice of an arbitrary presentation. Every chart satisfies `ν H x = C.word`.
  Quantifying over every chart, not a selected one, states agreement of local
  prescriptions, including overlapping neighborhoods, equivalent minimal envelopes
  and the controlled-transform representatives. `pointed` identifies the point on
  each etale chart with its ancestor in the actual history.
- The simultaneous assignment is `∃ ν : ValueFamily.{u} ResolutionWord`; all assertions
  concern `Admissible ν H`, exactly the existing least inductively generated class.
  There is no termination assumption, no completed tower and no arbitrary externally
  supplied class of admissible histories.
- Finite image is `(Set.range (ν H)).Finite`; closedness is
  `∀ v, IsClosed {x : H.X | v ≤ ν H x}`. The regular-locus clause is the exact
  equivalence `ν H x = ⊥ ↔ IsRegularLocalRing (H.X.presheaf.stalk x)`.
- `sumResolutionWord` fixes bottom and the entire tail and applies the existing
  `sumHead D` to the head. For every bound
  `topologicalKrullDim H.X ≤ (D : WithBot ℕ∞)` the final conjuncts preserve and reflect
  both `≤` and equality for every pair of stage points. Equality of fibers therefore
  gives exactly the same equality strata. The assignment and its value space are
  outside the `D` quantifier, expressing independence of this auxiliary bound.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` / `Separated`: `IsSeparated`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`. These occur through `EmbeddedResolutionPair`.
- `Sheaf.AlgebraicGeometry.EmbeddedResolutionHistory`:
  `EmbeddedResolutionHistory`, `.X`, `.ValueFamily`, `.Admissible`, and its actual
  diagram maps and intrinsic center kernels.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`;
  `WeilConjectures.Compactification.StrictTransform`: `strictTransform`,
  `strictTransformMap`, `strictTransformToSource`. These are used by the existing
  embedded and controlled history definitions, and are not reconstructed here.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, through the pair
  interface; the point criterion uses the same `IsRegularLocalRing` predicate.
- `Sheaf.AlgebraicGeometry.HilbertSamuelSmoothDimensionProfile`: `DimensionHead`,
  `normalizedHead`, `sumHead`, its integer summation/difference and numerical theorems.
- `Sheaf.AlgebraicGeometry.HilbertSamuelReachableLevels`, publicly importing
  `HilbertSamuelLocalPresentations`: `local_minimal_presentations`,
  `presentation_full_maximalOrder`, `Presents`, `MinimalAt`, `FullMaximalOrder`.
- `Sheaf.AlgebraicGeometry.MarkedIdealNumericalResolutionEngine`, publicly importing
  `MarkedIdealInvariantData` and `MarkedIdealData`: `NumericalResolution`, `Word`,
  `rational`, `History`, `Admissible`, `IsMaximalOrder`, and `HistoryStep`.
- `Sheaf.AlgebraicGeometry.MinimalEnvelopeCoefficientComparison`:
  `coefficientHistoryBoundary`, `coefficientIntrinsicBase`, and the comparison theorem
  `minimal_envelope_coefficient_comparison` (the latter supplies the proof plan).
- `Mathlib.RingTheory.Length`: `Module.length`;
  `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, through the existing head.

All recorded, stated proof dependencies are imported. Those already present through
public statement imports are not duplicated. The remaining proof imports are the
upstream affine blowup definition, reduced scheme image theorem, Mathlib Noetherian
schemes, universally open morphisms, and Noetherian-space compactness. The docstring
contains all nine proof steps with their numerical, presentation, comparison,
finite-cover and local-upper-bound arguments. Every delivered declaration has the
source and blueprint tag. `autoImplicit false` binds all universes and variables.

Edge cases checked before writing and in a second self-check of the signatures:
empty strict transforms have no chart obligation, empty range and empty upper levels;
regular points use bottom without demanding a finite-order zero-ideal presentation;
zero-length histories have suffix length zero and do not require any centers;
`D = 0` is included whenever the stage has dimension at most zero; negative integer
finite differences remain integers; finite disjoint unions require no connectedness;
nonclosed points use local component dimensions rather than global dimensions;
identity intrinsic blowups retain their center kernels and chronological boundary
positions; auxiliary `D` is not an argument of the value assignment or value space.

Searches performed with the required launcher wrapper:

- LeanFinder: "Gluing normalized Hilbert Samuel heads and marked ideal resolution tails
  into a finite upper semicontinuous invariant on admissible embedded blowup histories".
  Eight results, including `Scheme.IdealSheafData.glueDataObj` and unrelated prime-chain,
  normalization and structure-sheaf statements; none states the required gluing theorem.
- Loogle: `WithBot, Lex, List`. Zero matches for a combined existing interface.
- Mathlib grep: `HilbertSamuel|NumericalResolution|normalizedHead`. Zero hits.
- Project rg: `normalized.resolution|NormalizedResolution|normalizedHead` and the
  exact node id in `lean/WeilConjectures`, `lean/Sheaf`, and the upstream name index.
  This found the recorded dimension-head definitions and unrelated derived-resolution
  comparisons; no existing gluing statement or local-chart interface.
- DAG/blueprint search: `blueprint_refs.py search 'normalized resolution word'` returned
  zero blueprint nodes; the DAG contains this gluing item and its later consumers.
  The helpers are parts of this item's own local prescription, not new independent
  notions. The repair below adds ownership of the existing chronological boundary through
  a new definition node, without introducing another Lean definition.

Source checked: the actual ILO PDF, printed pp. 93--94 (PDF pages 99--100),
Remarks 2.3.11 and 2.3.13, and the current blueprint unit under
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`.
ILO refers to BMT section 6.3 for synchronization; the node's detailed assembly remains
its explicitly agent-written argument. No source claim was inferred from an unrelated
general desingularization statement. No statement correction or dispute is recorded.

Validation: the final module compiled separately in sandbox and library module mode
through `scompile.py`, with no errors or warnings. No library build or direct repository
mutation was used. The requested dry-run and delivery gates follow this report.


## Repair of return H2

The saved packet was first dry-run unchanged: commit `e52f15e080d` passed the
mechanical preflight and compile. It still needed the independent review's mathematical
ownership correction. Compared with current main, the saved item differed only in
`lean` and the addition of the comparison theorem to `stmt_deps`; no other split or
statement field differed. This repair replaces that addition with
`def-trf-chronological-history-boundary`. The theorem remains in `proof_deps`.
The Lean module and every signature are unchanged from the reviewed packet at
immutable head `1add4b55f2dc`.

The advisory about `DimensionHead`, `normalizedHead` and `sumHead` was checked against
`HilbertSamuelSmoothDimensionProfile.lean:76--90`: these too have concrete data and
are reused literally. Their existing profile node is a base statement dependency;
this repair introduces no additional theorem dependency for those definitions.

## New nodes

`def-trf-chronological-history-boundary` defines the ordered boundary recursively on
all raw embedded histories, with no admissibility or termination assumption. It records
`existing: true` for
`AlgebraicGeometry.EmbeddedResolutionHistory.coefficientHistoryBoundary` in the unchanged
module `Sheaf.AlgebraicGeometry.MinimalEnvelopeCoefficientComparison`. The initial list
is empty; `Fin.induction` maps each old ideal to the kernel of its strict-transform map
and appends the center kernel pulled back along the actual history transition. List order
and identity-stage entries remain. This is the bookkeeping in ILO VIII 2.3.11--2.3.13's
resolution input, made explicit by the existing comparison node's step 7 and the item's
steps 3--5. The definition node cites the raw history, schematic strict transform and
ordinary blowup definitions; it does not cite a comparison theorem for its data.

New searches ran through `msearch.py`: LeanSearch's query about the chronological
exceptional boundary returned eight unrelated smooth-locus, homological-boundary,
manifold, composition and co-Heyting results; Loogle's `"coefficientHistoryBoundary"`
returned zero hits; Mathlib grep for
`coefficientHistoryBoundary|chronological.*boundary|history.*boundary` in
`AlgebraicGeometry` returned zero hits. Project/DAG `rg` found exactly the existing
plain definition and its uses, with only the comparison theorem's node listing the
name. `blueprint_refs.py search 'chronological history boundary'` returned zero blueprint
nodes; `ancestor` identified `lem-trf-local-term-locality`. Search outputs are preserved
in the node's `mathlib_searches` and the wrapper's `searches.jsonl`.

## Second reading by O1

Self-check performed in this repair session, with the node, unchanged module and new
boundary node open; no separate agent was started, as the dispatcher's brief prohibits
it. The original clause-by-clause mapping above was reread: the fixed engine binder,
actual-history chart, empty fresh-test boundary, retained-head suffix, leading-one drop,
agreement for every chart, finite image, closed upper levels, regularity equivalence
and both summation comparison equivalences still match the item. There is no change
to any hypothesis or conclusion. `ResolutionWordChart.boundary` uses only the concrete
`H.coefficientHistoryBoundary` definition, now named by the new definition node, and
not the comparison theorem. The comparison theorem is still available for proof steps
3--5 through its existing public module import.

The new node was checked against the full recursive body, not just its type: at stage
zero it is `[]`; old entries use `strictTransformMap ... .ker`, hence schematic image
ideals; the new entry is exactly `(H.centerToIntrinsic j).ker.comap` along the actual
intrinsic transition. The recursion retains entries even for intrinsic identities and
requires no reducedness or smoothness at later stages. Zero-length and empty-scheme
histories are included. No Lean data, theorem, statement correction or additional
sorry is introduced by this ownership repair.

Repair validation: `scompile.py` compiled the unchanged delivered module in sandbox
and library mode without errors or warnings. The first repaired-packet preflight
required the common node field `import_flags`; an empty list was added as directed
by that concrete diagnostic. The signature and dependency self-check passed.
