## Worker report

Stage 2 statement delivery, not a reopening of NP's accepted stage-1 split. The inherited
unchanged-item refusal was a stage-1 refusal; coord/brief-stage2.md §0 explicitly directs this
stage-2 assignment to proceed. The item's current queue row is stage 2 and it had no lean record.
No mathematical statement, proof plan, source, status, or dependency list was changed.

MinimalEnvelopeCoefficientComparison.lean states the entire node in twenty declarations, including its common-germ comparison helper.
All postponed proofs are whole named theorem proofs `by sorry`, with the owning blueprint id,
source and the corresponding natural-language proof steps. Definitions contain real data.

Hypothesis and clause correspondence:

- Reduced finite-type rational X: `[IsReduced X]`, structure map to
  `Spec (.of (ULift.{u} ℚ))`, `[LocallyOfFiniteType p] [QuasiCompact p]`. The lift only
  places Q in the same universe as the schemes. Point a is an arbitrary scheme point.
- Minimal smooth local envelope: the existing `p.IsMinimalSmoothEnvelope i a`, which says
  closed immersion, smooth ambient, and invertibility of the canonical differential-fibre
  map. `coefficient_minimal_envelope_exists` supplies its pointed open neighborhood.
- Regular coefficient data: the exact recorded `RegularHilbertCoefficientDatum`, including
  its common affine etale chart D.e, coefficient subspace D.N, five formal conditions and
  diagonal Taylor expansions at possibly nonclosed points. `orderedVertices α` gives the
  ordered, incomparable, essential transverse vertices specified in the dependency node.
- Positive common multiple: `IsCommonCoefficientMarking α b`, including divisibility by
  every positive weight `(α l).degree - γ.degree` and `s = 0 → b = 1`.
- The displayed I: `D.markedCoefficientIdeal b` is `ofIdealTop` of the ideal spanned by
  exactly `D.coeff l γ ^ (b / ((α l).degree - γ.degree))` for `γ.degree < (α l).degree`.
  Its coherence is the named `markedCoefficientIdeal_coherent` theorem. The empty generator
  set constructs the zero ideal. `coefficientMarked` uses precisely D.N, D.j, I and b.
- H0 and intrinsic embedded chart: `coefficientAmbient` uses the actual fibre product
  `pullback i D.e`, its second projection, `HilbertSamuel.function (i ≫ p) a`, and boundary
  `[]`. No arbitrary embedded replacement or arbitrary level is allowed.
- Supplied finite-test presentation: the existing `HilbertSamuel.Presents
  (D.coefficientMarked b hb.1)` is the hypothesis in the suspension and comparison assertions.
- Positive singular transverse rank: `coefficient_transverse_rank_pos` concludes `0 < n`
  from `¬ IsRegularLocalRing (X.presheaf.stalk a)`. The datum's n is the essential transverse
  rank; its defining n equations and invertible Jacobian fix the codimension.
- Retraction coordinates after localization: `coefficient_retraction_exists` supplies a
  pointed etale chart and the existing Cartesian `SuspensionChart` of rank n. Subsequent
  formula assertions are written on such a chart, exactly as the node's local convention.
- Explicit J: `suspendedCoefficientMarked` has full ambient support, identity embedding,
  marking b, and exactly `MarkedIdeal.suspension c.retraction c.parameters I b`, the existing
  construction `(z_1^b,...,z_n^b)+p^*I`. A named theorem supplies its coherence. The theorem
  `coefficient_suspension` gives presentation, every finite test via `Equivalent`, and
  `FullMaximalOrder` when a is singular. In particular no arbitrary full-support ideal is
  accepted as the specified suspension.
- Regular codimension-zero germ: `regular_codimension_zero_coefficient_presentation`
  supplies an open smooth chart, identity-up-to-iso intrinsic and marked embeddings, the
  zero ideal, marking one, presentation of H0, and order `⊤` at every point. It asserts no
  finite order here, and imposes no bound on the point's residue transcendence degree.
- Two minimal envelopes of an identified pointed intrinsic germ: `HasMinimalEnvelopeCoefficientComparison`
  quantifies over both smooth embeddings, their maps over the given intrinsic structure
  maps, both minimality conditions, both independent regular data and common markings,
  and either the original datum or its local suspension (the existing `IsLocallySuspended`).
  `minimal_envelope_coefficient_comparison` asserts this predicate for every rational
  isomorphism `e` and point a of reduced finite-type schemes. An isomorphism of chosen
  neighborhood representatives encodes the given germ isomorphism; restriction is allowed.
- Common pointed etale comparison: `CommonEtaleGermComparison` records the two etale maps,
  both Cartesian embedded pullbacks and zero-dimensional `Pullback` predicates, the actual
  commuting maps to the specified original intrinsic identification, a lifted point mapping to both specified D.center points, and
  equality of actual ordered ideal pullbacks. It does not require the two entire intrinsic
  coefficient neighborhoods to be isomorphic.
- Every specified finite ordered earlier-center list: `earlier : List X.IdealSheafData`,
  ambient lifts `(J.map i₁).comap D₁.e` and `((J.comap e.inv).map i₂).comap D₂.e`, and
  `C.earlier`. These are the actual preimage ideals of the closed quotient maps, not arbitrary
  ambient lifts, supports, radicals, or unordered sets.
- Same finite tests: `HasComparedCoefficientTests` supplies actual marked pullbacks
  P',Q' to C.W, their presentations, and `Equivalent P' Q'`. It does not identify their
  ideals or markings. `Equivalent` quantifies over every finite depth, all allowed next
  operations, existence of transforms, and every pair of the specified transforms.
- Commutes with restriction: the same predicate quantifies over every further open map v
  and embedded `Pullback v 0`, and every actual pair of marked pullbacks, concluding their
  presentations and equivalence. Ideal equalities and the pointed comparison restrict.
- Histories: `coefficient_comparison_after_admissible_histories` takes the recorded
  `Admissible ν H`, `Admissible ν K`, and `IntrinsicComparison e H K`. The latter retains
  the entire natural isomorphism and each chronological center ideal, including identity
  intrinsic blowup stages. The explicit over-Q and `hlevel` hypotheses are precisely the
  statement's identified current germs and retained levels, not an ambient identification.
- Induced ordered boundaries: `coefficientHistoryBoundary` is Fin.induction starting from
  `[]`, taking each actual schematic strict transform off the new intrinsic center and
  appending the extended intrinsic center ideal. The history theorem concludes stagewise
  equality under the given natural isomorphism. The current coefficient comparison is also
  concluded, with all future test boundaries restarted as `[]`; the earlier ordered ideals
  can be supplied to it without becoming test boundary components. Raw diagrams are used
  without assuming smoothness or reducedness of later stages; the comparison assertion
  quantifies over any supplied current minimal smooth envelopes and coefficient data.

Dependency declarations read and reused:

- Mathlib.AlgebraicGeometry.Properties: `AlgebraicGeometry.IsReduced`.
- Mathlib.AlgebraicGeometry.IdealSheaf.Basic: `Scheme.Hom.ker`, `Scheme.IdealSheafData.ofIdealTop`;
  Functorial: actual `map` and `comap`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth, Etale, ClosedImmersion, FiniteType:
  `Smooth`, `SmoothOfRelativeDimension`, `Etale`, `IsClosedImmersion`, `LocallyOfFiniteType`;
  finite type additionally uses QuasiCompact, as in the recorded envelope interface.
- Mathlib.RingTheory.Kaehler.Basic: `KaehlerDifferential`; the envelope predicate uses the
  existing canonical relative differential pullback, stalk and residue-fibre map.
- Sheaf.AlgebraicGeometry.HilbertSamuelInvariant: `HilbertSamuel.function` and `summation`.
- Sheaf.AlgebraicGeometry.MarkedIdealOrder: `HilbertSamuel.stalkIdeal` and `order`.
- Sheaf.AlgebraicGeometry.HilbertSamuelPresentation: `Embedded`, `Marked`, `Presents`,
  `Equivalent`, `Pullback`, `MarkedPullback`, `FullMaximalOrder`; all their recursive test
  geometry is reused without a duplicate definition.
- Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum:
  `HilbertCoefficient.RegularHilbertCoefficientDatum` and `orderedVertices`.
- Sheaf.AlgebraicGeometry.CoherentFiniteType: `Scheme.Modules.IsQuasiCoherentFiniteType`.
- Sheaf.AlgebraicGeometry.IsRegularScheme: recorded regularity uses Mathlib's
  `IsRegularLocalRing` on the actual local ring.
- Sheaf.AlgebraicGeometry.MinimalSmoothEnvelopeComparison:
  `Scheme.Hom.IsMinimalSmoothEnvelope`, `Scheme.exists_minimal_smooth_envelope`,
  `Scheme.Hom.exists_common_etale_minimal_smooth_envelopes`, and
  `Scheme.Hom.exists_etale_smooth_closed_pair_retraction`.
- Sheaf.AlgebraicGeometry.MarkedIdealTransverseSuspension: `suspension`, `SuspensionChart`,
  `IsLocallySuspended`, and `transverse_suspension`.
- Sheaf.AlgebraicGeometry.EmbeddedResolutionHistory: `EmbeddedResolutionHistory`,
  `IntrinsicComparison`, `Admissible`, the intrinsic diagram, its actual centers and base map.
- WeilConjectures.Compactification.StrictTransform: `strictTransformMap`.

All already-stated proof dependencies are imported. The two proof-only nodes
lem-trf-diagonal-taylor-faithful-flatness and lem-trf-coefficient-test-sequence-propagation
currently have no Lean record or Mathlib match, so they have no module to import. Their
mathematical use is explicitly recorded in the theorem docstrings for stage 3. They are not
missing notions needed to type these statements.

Edge cases read against the definitions: empty vertex list and n=0; positive mark one for
an empty list; I=0 with positive transverse rank; singular versus regular stalk; nonclosed a
and the diagonal residue-field Taylor convention; empty cosupport and empty centers in the
existing finite tests; independent choices of b, coefficient ideals and etale neighborhoods;
zero-length history; identity intrinsic blowups; ordered repeated/empty boundary components;
all scheme universes u (Q lifted without forcing u=0); open restrictions and zero relative
dimension; nonsmooth later raw-history stages. No statement dispute or correction is asserted.

Searches made using the prescribed msearch.py wrapper:

- leanfinder: “Minimal smooth local envelopes Hilbert Samuel coefficient ideal suspension
  common etale comparison of finite marked ideal tests”: eight hits on Algebra.IsEtaleAt,
  StandardEtalePair, smooth polynomial charts and smooth loci; no statement match.
- loogle: `AlgebraicGeometry.HilbertSamuel.Equivalent,
  AlgebraicGeometry.Scheme.Hom.IsMinimalSmoothEnvelope`: zero hits / unknown first identifier.
- grep Mathlib AlgebraicGeometry: `MinimalSmoothEnvelope|RegularHilbertCoefficient|
  coefficientIdeal|transverse_suspension`: zero hits.
- leansearch: “Hilbert Samuel marked coefficient ideal minimal smooth envelopes comparison
  suspension”: eight hits, leading coefficient ideals, smooth locus, homogeneous ideal core,
  polynomial smoothness; no comparison theorem.
- rg of lean/WeilConjectures and lean/Sheaf for regular coefficient data, coefficient ideals,
  minimal smooth envelopes, and the exact item id: found the dependency modules listed above,
  no theorem giving this full statement. MarkedIdealInvariantData.coefficientIdeal was read:
  it is the logarithmic-derivative/factorial companion construction, not the supplied regular
  coefficients' common-weight ideal here. It must not be substituted for this formula.

Validation of the returned packet was clean. The repaired single-module delivery compiled through scompile.py in sandbox mode
(4.5 s) and normal library mode (5.0 s), with no errors or warnings. No linter is disabled.

## Second reading by ND

Self-audit after opening the final item module and both node statements: the above correspondence
was checked against all hypotheses and all clauses. A final point audit added `pointS`
and `pointT` to the germ comparison, requiring the common point to land at both specified
coefficient-chart centers, in addition to lying over the original intrinsic point. The initial draft compared whole chart
schemes; the item-owned helper removes that extra global-isomorphism demand. The explicit
suspension is constructed, rather than assumed to exist as an unspecified ideal. The history
assertion no longer imposes reducedness or finite-type hypotheses on raw later stages; the
comparison quantifies over supplied current envelopes, as the node does. Empty test boundary
and earlier chronological centers are distinct throughout. All zero-ideal and rank-zero
clauses remain present. This is a self-audit, not an independent worker reading: the dispatcher
explicitly forbids starting other agents, and the maintainer supplies independent review.

## Returned-delivery repair (H13)

The independent review of immutable head dbb85837d1db accepted the mathematics but
returned the dependency-record rebinding. The saved packet's initial dry run passed
(commit 7eb56f01f10); that mechanical pass did not repair H13.

CommonEtaleGermComparison now belongs to MinimalEnvelopeCoefficientComparison.lean and
is listed in the item's lean.declarations. Its fields and signature are unchanged; its
source/blueprint docstring now names this item. The item imports the original
HilbertSamuelPresentation module directly. The separate HilbertSamuelEtaleGermComparison
module is removed from the packet, and def-trf-hilbert-samuel-presentation.json is restored
byte-for-byte from the live read clone, retaining Q79's module, Presents declaration,
statement, file, authorship and complete lean record. No dependency record is changed.

The helper is the interface for this item's common pointed etale comparison clause,
not a replacement for the landed presentation notion. No theorem signature, definition
body, hypothesis, conclusion, item statement or dependency list changes in this repair.
The self-check compared the moved helper field-by-field and rechecked the item record's
verbatim main signature and explicit universes. A fresh source search of lean/Sheaf and
lean/WeilConjectures for CommonEtaleGermComparison found no existing declaration.

Repair self-check passed: dependency node byte equality, item fields unchanged outside lean,
verbatim main signature, twenty listed declarations, no stale sibling import and Lean line widths.
