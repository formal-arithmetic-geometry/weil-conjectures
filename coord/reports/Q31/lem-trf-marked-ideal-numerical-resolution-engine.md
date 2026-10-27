## Worker report

This repaired packet states
`AlgebraicGeometry.MarkedIdeal.exists_numerical_resolution` in
`Sheaf.AlgebraicGeometry.MarkedIdealNumericalResolutionEngine`. Its whole proof is
`sorry`. It asserts `Nonempty NumericalResolution.{u}` with the simultaneous value
assignment and all geometric, invariance and termination conditions below. Definitions
have real data; no proposition is proved. The theorem docstring preserves the node's
complete ten-step proof. The engine's informal statement and proof are unchanged.

The saved report and packet were read first and the prescribed initial
`deliver2.py ... --no-push` was run: it passed as `95682d20e52`. That mechanical pass
still contained the collisions identified in the immutable-head return, so those were
repaired before delivery. The current packet was compared field by field with the
current read-only main tree. Only the engine's `lean` and its two new definition
dependencies differ there; the two definition nodes are new. No dependency binding is
changed. The released stage-1 re-split note was read; this stage-2 delivery retains
that proof plan, as the return directs.

Hypotheses and objects, clause by clause:

- Over Q and arbitrary scheme universe: `MarkedIdeal.ambient` is Q79's
  `HilbertSamuel.Embedded (ULift.{u} ℚ)`. The existing `p` and `smooth` provide the
  rational smooth ambient; the imported Mathlib ULift field instance supplies the
  same rational field in every universe.
- Smooth closed support, coherent ideal and positive integral mark:
  `MarkedIdeal.marked : HilbertSamuel.Marked ambient` reuses `N`, `j`, `closed`,
  `smooth`, `ideal`, `coherent`, `marking`, `positive`. In particular `coherent` is
  Q25's `Scheme.Modules.IsQuasiCoherentFiniteType ideal.toModules`. Smooth support
  over a field is locally Noetherian, where this is the coherent-ideal condition.
  The finite-type hypotheses are the four fields `finiteTypeAmbient`,
  `compactAmbient`, `finiteTypeSupport`, `compactSupport`, using the recorded
  local-finite-type plus quasi-compact conjunction. There is no separatedness,
  equidimensionality, nonemptiness, proper-ideal or nonzero-ideal assumption.
- Finite ordered smooth hypersurfaces: use the existing `ambient.boundary : List`;
  `cartier` requires its effective Cartier ideals and `smoothBoundary` their
  smoothness over Q. The members need not be connected or irreducible.
- SNC and transversality: `snc` is Q74's
  `HasAdaptedNormalCrossingsCenter ⊥ (fun i ↦ ambient.boundary.get i)`.
  The bottom ideal has the whole ambient as its support, so its adapted-coordinate
  condition checks SNC everywhere. `transverse` is the same predicate on the support,
  with the boundary pulled back by `marked.j`; `transverseCartier` records those
  hypersurface ideals. The existing definition supplies affine equations, distinct
  regular parameters, and unit ideals for labels absent near the point.
- Cosupport: `MarkedIdeal.cosupport` is the inverse image of the EXISTING
  `marked.cosupport` along `marked.j`. The latter is `j '' {x | b ≤ order I x}`.
  Since the recorded closed immersion is injective, its inverse image is exactly
  the support-point order-at-least-b locus. `IsMaximalOrder` uses Q79's `order I x = b`
  on that locus. The coefficient formulas use `HilbertSamuel.stalkIdeal` directly;
  no affine-germ or maximal-power definition is copied.
- Admissible controlled transforms: `HistoryStep.step` is the existing
  `HilbertSamuel.Step`; `kind` selects `admissibleBlowup`, `admissible` uses the
  existing marked cosupport and `transforms` is `Step.Transforms`. Its geometry gives
  the actual ambient blowup, smooth adapted center, old strict boundary followed by
  the exceptional ideal. Its transform gives the strict support and
  `I' * E^b = pullback I`. `exceptionalInvertible` records division by an invertible
  ideal on the new support. The retained support map and `centerToSupport` are pinned
  by their commuting triangles with the closed immersion; these uniquely specify
  the maps used in the history, rather than allowing arbitrary maps.
- Test equivalence: `HistoryEquivalence` identifies the ambient diagrams, bases,
  ordered boundaries, centers and births. `comparisonPullback` transports the second
  marked object using Q79's `MarkedPullback`; `equivalent` uses Q79's `Equivalent`
  on the common ambient. Its depth-zero clause identifies cosupports, and every
  successor quantifies over every test and every pair of transforms, including
  existence of both transforms. Q79's `Step`/`Transforms` already supplies line
  products appending the actual zero section and exceptional-intersection blowups
  with ordinary ideal pullback. There is no second test-operation calculus or
  ambient-diagram realizability predicate. Open restrictions are the open smooth
  history pullbacks, with the same existing marked-pullback relation.
- Histories: `History.state`, `step`, `birth`, `initialBirth`, `inheritedBirth`,
  `exceptionalBirth` retain the controlled stages and ordered births. `Extension`
  preserves every preceding state, step and birth by equality/HEq.
- Smooth history pullback: `HistoryPullback` uses stagewise smooth ambient maps,
  `MarkedPullback` and the cartesian support maps, preserving base, boundary, centers,
  step diagrams and births. It imposes no constant-relative-dimension hypothesis and
  retains empty pulled-back centers. The extra embedded `X` and retained `level`
  in the reused Q79 input have no presentation/level-locus condition: every marked
  ideal can be used, for example with the identity embedded ambient and any level.

Conclusions, clause by clause:

- One assignment for all inputs and finite histories is `NumericalResolution.value`
  of type `ValueFamily`. `Admissible` generates exactly initial histories,
  maximum-center steps, empty stages, and smooth pullbacks.
- `Word = List Entry` uses the existing lexicographic list order. `Entry` is the
  fixed ordered tagged sum of rational orders, natural counts and monomial tuples
  with a top infinity terminal. The empty continuation is smallest.
- `recursion` requires a `TailCertificate` for the remaining word. Its positive
  constructor records a `CoefficientReduction`: actual boundary monomial and
  residual factorization, exact residual order, its rational normalization,
  birth-selected old components and their count, companion formula, old-boundary
  augmentation, logarithmic derivative coefficient ideal with factorial mark,
  actual local-ring restriction, and the maximal-contact parameter equation.
  The next support is a smooth hypersurface with strictly smaller stalk dimension;
  retained component births are inherited.
- The zero-ideal terminal is `IsTerminal` with `stalkIdeal = ⊥` and `[terminal ⊤]`.
  The monomial terminal is `[rational 0, terminal Γ]`, with `IsMonomialValue`
  requiring the actual factorization and minimal subset cardinality, maximal
  normalized sum, then maximal ordered index tuple.
- `normalized` requires first entry `rational 1` on maximal-order inputs. The
  leading companion header is separated from the certified residual tail, as in
  proof step 1.
- `equivalentTails` equates `.drop 1` for corresponding cosupport points of the
  identified test-equivalent histories, with equality of the two SUPPORT STALK
  `ringKrullDim`s at those points. No whole-support dimension is substituted.
- `smoothValues` compares the whole word through the actual cartesian support map,
  with no dimension-equality or relative-dimension restriction.
- `finiteImage` and `semicontinuous` give finite image and closed upper-level sets
  on each admissible cosupport.
- `maximumExists` supplies an extension whose full center image is exactly
  `maximumLocus`. The existing step's geometry supplies smoothness, closedness
  and adapted normal crossings. `strictProgress` puts every surviving value below
  every old maximum. `outsideCenter` preserves values away from that center.
- `termination` excludes an infinite compatible tower of these maximum steps.
  No well-foundedness of the entire numerical order is assumed.
- `PatchedPresentations` gives a finite ambient open cover, overlap restrictions,
  actual cartesian overlap squares and equivalent histories. Its `dimension`
  clause compares stalk Krull dimensions at every pair of corresponding cosupport
  points. `IsSynchronizedStep` takes the maximum over the union and allows empty
  centers on patches missing it. `synchronizedExists`, `patchedCenters`,
  `synchronizedProgress` and `synchronizedTermination` give existence, gluing of
  actual center ideals to a smooth global center, strict progress and termination.
- Dimension descent is in every positive coefficient certificate; infinity and
  explicit monomial data give its terminal alternatives. `noFixedPrefixTail`
  excludes infinite maximum-step tails with all earlier entries fixed. These are
  controlled marked-ideal transforms, not strict transforms of singular schemes.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.HilbertSamuelPresentation`: `HilbertSamuel.Embedded`,
  `Marked`, `Marked.cosupport`, `Step`, `Step.Admissible`, `Step.Transforms`,
  `EquivalentThrough`, `Equivalent`, `MarkedPullback` (Q79).
- `Sheaf.AlgebraicGeometry.MarkedIdealOrder`: `HilbertSamuel.stalkIdeal`, `order` (Q79).
- `Sheaf.AlgebraicGeometry.AdaptedNormalCrossingsCenter`:
  `HasAdaptedNormalCrossingsCenter` (Q74), on the bottom ideal for SNC.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType` (Q25), through `Marked.coherent`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `ClosedImmersion`, `FiniteType`,
  `QuasiCompact`: the recorded `Smooth`, `IsClosedImmersion`,
  `LocallyOfFiniteType`, `QuasiCompact`.
- `WeilConjectures.Blowup.Gluing`: ideal-sheaf `blowup`, `blowupMap`;
  `WeilConjectures.Compactification.StrictTransform`: `strictTransform`,
  `strictTransformMap`, `strictTransformToSource`, used through Q79's step.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`: `IsInvertible`;
  Q74 reuses `IsLocalRing.IsRegularSystemOfParameters`.
- Mathlib's list/sum/product lex orders, rational order, `Derivation`, and ULift field.

The main theorem imports all currently recorded proof inputs:
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`,
`Sheaf.TraceFormula.SmoothGeometricallyNormal`, and the newly landed
`Sheaf.AlgebraicGeometry.MarkedControlledBlowupCharts`. The residual-companion and
logarithmic-coefficient nodes still have no recorded Lean module; they remain in
`proof_deps` and the full proof docstring. No new proof node is introduced.

Edge cases rechecked after replacement: empty support/cosupport; unit ideal (order
zero and empty positive-mark cosupport); zero ideal (infinite order and possible
component deletion); empty boundary and parameter lists; disconnected boundaries;
non-pure-dimensional smooth inputs; a center contained in boundary components;
empty centers retained after restriction; arbitrary smooth relative dimension;
line products with zero section and exceptional tests with ordinary pullback;
depth zero in `EquivalentThrough` (cosupport equality); no restriction from the
auxiliary Hilbert--Samuel scheme/level on the initial marked data. Empty patched
families cover only the empty ambient. Equal global dimension with different local
stalk dimensions does not identify tails.

Searches: the original packet's verbatim search records are retained in both new
nodes. Fresh LeanFinder, LeanSearch, Loogle and Mathlib grep queries were run for
this repair and appended with their exact returned logs. LeanFinder on “marked
ideal resolution invariant finite histories boundary birth stages numerical
coefficient recursion” returned Chevalley complexity and regular-sequence recursors;
LeanSearch on “marked ideal numerical resolution invariant birth history” returned
invariant-basis-number, ideal-filtration, projective-resolution and ideal-height
hits. Loogle on `AlgebraicGeometry.HilbertSamuel.Equivalent` returned unknown
identifier (it indexes Mathlib, not the project); Mathlib geometry grep on
`MarkedIdeal|NumericalResolution|HistoryEquivalence|TailCertificate` returned zero
hits. The project/DAG searches POSITIVELY found Q74/Q79, Q26's suspension and Q13's
controlled charts. The first two provide the reused notions; the latter two provide
statements, not a birth-history/numerical-certificate definition. The upstream
WeilConjectures history/numerical query returned no hits; blueprint_refs search
“marked ideal” returned 0 nodes. Historical “no marked framework” conclusions in
the saved packet describe the earlier search only and are superseded here.

Sources read: the saved ILO text at printed pp.93--94 and full BMT text at sections
5.1--5.4, in particular the actual definitions and Remark 5.1 at pp.9--10. The
explicit monomial tie-breaking, alphabet and fixed-prefix clauses are the engine
node's own construction. No source or target statement is corrected in this repair.

## New nodes

`def-trf-marked-ideal-data`, module `Sheaf.AlgebraicGeometry.MarkedIdealData`, now
only packages finite-type rational instances of Q79's `Embedded`/`Marked` and adds
`HistoryStep`, `History`, extensions, smooth history pullbacks, equivalent-history
comparisons and birth bookkeeping. Its statement explicitly cites Q74/Q79 and its
`stmt_deps` contains all three landed owner nodes. The private coordinate predicate,
SNC definition, affine-germ ideal, center/blowup/test operations and realizability
equivalence have been removed. Its two small support-locus/order predicates are
expressions in the existing `Marked.cosupport` and `order`.

`def-trf-marked-ideal-invariant-data`, module
`Sheaf.AlgebraicGeometry.MarkedIdealInvariantData`, retains the alphabet, numerical
assignment, coefficient/monomial certificates, admissible maximum histories,
patched presentations and `NumericalResolution`. It directly cites the existing
order node for every stalk ideal in its equations. The pointwise dimension repair
is retained. Every declaration has a source and blueprint docstring.

## Repair of immutable head e70183ab6d27

H12/H4, point 1: removed `BoundaryCoordinatesAt`, `IsOrderedSNC` and the copied
center coordinates. Both SNC checks use Q74 `HasAdaptedNormalCrossingsCenter` at
bottom, and actual centers use Q79 `Step.geometry`, which invokes the same owner.

H12/H4, point 2: removed `idealAt`; all coefficient equations use Q79 `stalkIdeal`.
Cosupport reuses `Marked.cosupport`, defined via `order ≥ b`; maximal order is
`order = b`. No order construction is duplicated.

H12/H4, point 3: removed `Center`, `BlowupDiagram`, `ControlledBlowup`, `Pullback`,
`SmoothPullback`, `ExceptionalBlowup`, `LineProduct`, `TestStep`, `RealizesTest`
and `TestEquivalent`. History edges carry Q79 `Step`, `Admissible`, `Transforms`;
comparisons use `MarkedPullback` and the depth-wise `Equivalent`. The only retained
edge data are canonical maps and the invertibility required by the engine's
controlled-division clause; their triangles pin the maps uniquely. New history
pullbacks do not invoke Q79 `Pullback`'s constant-relative-dimension condition:
`MarkedPullback` plus a smooth ambient map gives the required unrestricted notion.

Both earlier repairs are preserved: no `pqf-def-coherent.json` is delivered or
changed, and Q79 `Marked.coherent` uses the unchanged Q25 declaration;
`equivalentTails` and `PatchedPresentations.dimension` compare stalk Krull dimension
at corresponding cosupport points, without global dimension or extra pullback
hypotheses. No declarations are rebound and no existing owner node is edited.

## Second reading by Q31

I reread the engine statement and all three revised modules against BMT 5.1--5.4
and the return. Rational smooth finite-type data and coherence are retained through
Q79/Q25; positivity and empty-support cases remain. The existing test boundary has
no presentation-empty-boundary restriction here. Q79's `EquivalentThrough 0` supplies
cosupport equality, and its successor requires existence of both transforms, fixing
the earlier ambient-diagram interpretation. Its line and exceptional branches use
ordinary pullback; the blowup branch uses strict support and controlled ideal.
Q74's bottom-center predicate checks every point, while its real-center use checks
only the center and permits overlap of center/boundary coordinates. These replace
all three collisions identified by the maintainer.

The invariant module was reread after every projection migration: local dimension
comparisons in `equivalentTails` and `PatchedPresentations.dimension` refer to
`last.marked.N.presheaf.stalk`; coefficient formulas refer to the existing
`stalkIdeal`; maximum and patched center equations use the existing step center.
The fixed alphabet, recursion certificates, all invariance/progress/termination
fields and complete proof docstring remain. The engine's only changes are its
imports and Lean record; its informal statement/proof are unchanged. There is one
`sorry`, the whole proof of the named engine theorem, and none in definitions.

Validation: the three final modules compiled separately in dependency order through
`scompile.py`, with clean library checks (10.5 s, 10.2 s and 4.4 s). The earlier
missing ULift field import and line-length warnings were repaired and recompiled.
The final local self-check found exact declaration lists and verbatim signatures,
explicit universes and `autoImplicit false`, lines at most 100 characters, canonical
JSON formatting, exactly three node files and no dependency record changes. The
only `sorry` is the whole proof of `exists_numerical_resolution`.
