## What changed

Repair of C-240da (returned head 240da721ad9). OrdinaryFiniteP1Arrows and
OrdinarySupportedKummerSystem are restored byte for byte from published source,
including all definition bodies, elaboration contexts and generated auxiliary
constants. FiniteP1DiagonalAlpha and SupportedDerivedUnitForget are also restored
byte for byte; neither consumer needs an adaptation.

The new OrdinaryFiniteCoefficientRecords module holds the coefficient-level
canonical finite adjunction, normalized arrow pullback and direct-image
additivity. Proved equalities identify the published projective-line unit and Chern pushforward
with the recorded adjunction's components. OrdinaryFiniteConstantUnitComp proves
constant-unit composition and equations for the unchanged supportedDerivedUnit.
The component proof uses those equations explicitly, rather than changing the
published constructions that other proofs unfold.

The component formula combines the diagonal Picard identity and Chern pullback
naturality. The canonical first Chern arrow is the inverse of the existing proved
ordinaryFiniteClass bijection. Supported Chern normalization and uniqueness
identify the transported diagonal arrow with the sum of the base hyperplane
class and the supplied relative Chern arrow. Adjunction naturality, unit pasting
and direct-image additivity give the two required components. No arbitrary
witness of unproved mere existence supplies data.

The current source refresh supplies additional Kummer/Ext interfaces. Both
OrdinaryFiniteP1Kummer and OrdinaryFiniteClassArbitraryBase are now restored
verbatim to that current source, including all X7 additions. Their earlier F1
representation edits and corresponding change records are omitted. The cup
module still completes its two existing proofs and reuses the named objects.
Local proof-instance reuse in OrdinarySupportedChernNormalization and in the
final alpha construction of ProjectiveLineDiagonalData preserves their formulas.
No Challenge or adopted WeilConjectures file is changed.

ProjectiveLineDiagonalIntegrals now requests only the unique supported boundary
from the existing ordinary_supported_kummer_uniqueBoundary theorem. Its old
proof destructured unused Chern and transport witnesses. Profiling found about
40 seconds of kernel checking in both the published baseline and F1 overlay;
the smaller existing interface compiled the same theorem in 23.8 seconds.
Its signature and public imports stay unchanged. No new obligation is introduced.

The two ordinary-finite nodes preserve the latest published proof_origin and
append to the complete published lean.note. The repair first restored X5's
provenance; the subsequent X7 source refresh is also preserved verbatim rather
than reverted. The supported-kummer-system node likewise retains its published
note and origin, with an appended repair explanation.

## Proved and sorry left

Existing holes closed:

- AlgebraicGeometry.Etale.ordinaryFiniteP1_diagonal_kummer_component_formula
  (lem-sp-finite-p1-diagonal-kummer-component-formula).
- AlgebraicGeometry.Etale.integralClass_bijective
  (def-wf-ordinary-etale-cup), by the existing arbitrary-base comparison.
- AlgebraicGeometry.Etale.integralForget_isEquivalence
  (def-wf-ordinary-etale-cup), by the integer-module and sheaf equivalences.

New holes left, each a public theorem in its own module with source, complete
proof in words and matching node:

- AlgebraicGeometry.Etale.finiteP1_diagonal_picard
  (lem-sp-finite-p1-diagonal-picard). This is the dual diagonal ideal's Picard
  identity, without coefficients, cohomology, direct image, trace or splitting.
- (closed by the reviewer, see below) AlgebraicGeometry.Etale.ordinaryFiniteChern_pullback
  (lem-sp-ordinary-finite-chern-pullback). This is normalized scalar Chern
  pullback naturality, without a diagonal, decomposition, direct image or trace.

The item has zero direct holes; the packet has exactly these two holes. Closing
its one original hole by these two steps is a decomposition. The packet also
closes the two existing cup holes. These are packet counts, not a claim about
the pinned target-closure ledger. The repair adds no hole, and all construction,
uniqueness, additivity, equality and unit-composition APIs are proved.

All ten delivery modules compile against a fresh artifact set. The component check passed in
receipt 29df0bf6a3508955c08491c5. The revised unit proof passed in
32e219e187249a8609de933b; it keeps the adjunction record folded and checks
declarations synchronously. This repairs the 61-second first submission check
without changing a statement or splitting a file. The other
production receipts are 3de1d5818f08449001735ab1,
8f8787a1f8a9f3573e03e52c and 2091d7e8a6eb70e87de9d55c. The supported-unit equation
uses the existing proved ordinaryFiniteUnitPullback_hom interface and equations
for the full transformations before evaluation. Local reuse of the published
derived-category and degree-zero caches avoids changing published bodies.
Unused general coefficient wrappers have been removed.

Final compatibility validation covers 34 unchanged consumers: all direct
importers of changed existing modules, their declaration/unfolding users,
the review's 21 modules, and the relevant quarantined consumers. Thirty-two consumers passed, including all fifteen consumers of the new component
API. The two independent timeouts reproduce on the published baseline. All 34
results and individual receipts are recorded in
coord/changes/F1-ordinary-finite-coefficient-interface.md. Validation copies are omitted
from the delivery; no source or quarantined module is withdrawn.

Two independent consumers also fail without any F1 overlay. GeoP1Cohomology
has no changed F1 module in its import closure and reaches the same time limit
in baseline receipt bf3b2de5c04c4cef31c4201f and overlay receipt
b025c63a53cfeaffc23e5356 (final refreshed check). The quarantined
AlgebraicGeometry.ProEtaleProjectiveLineTrace
exceeds the limit both with the final overlay (128e4ec2eed9effea9140127) and without it
(a8a7be6c6232d2d679bcd6e8). Neither source is adapted for a baseline failure.
The conservative earlier manifest of 335 files was used for preliminary checks
(135 distinct successful consumers); those checks span a source refresh and
are not claimed as the final validation.

## No longer needed

No existing public import is removed, no module is withdrawn, and no module is
claimed pruned from the targets' closure. The unit's statement and realized
steps remain in the route. The former direct dependency
def-kun-unbounded-exchange is replaced in the component calculation by ordinary
adjunction naturality and canonical constant-unit composition; its module
remains publicly imported by OrdinaryFiniteP1Arrows and needed in the library.
The chart/divisor-line dependencies are retained in the Picard step, the
supported Kummer dependency in the supported Chern normalization, and the
arbitrary-base comparison in the canonical Chern construction.

The returned changes to the class-domain, published arrow and supported-unit bodies, and the
resulting adaptations of FiniteP1DiagonalAlpha and SupportedDerivedUnitForget,
are no longer needed. Their associated adaptation records are removed from the
packet. The unused general coefficient wrappers and the intermediate
cached-functor conversion theorem are omitted. The component proof imports
OrdinaryFiniteConstantUnitComp directly
for its equality interface; no published module acquires this import.

## Where the brief, the DAG or earlier work was wrong

The returned representation change preserved mathematical values but broke
existing definitional unfolding and removed ordinaryFinitePullback._proof_1.
The previous eighteen-file validation missed the 21 consumers identified by
C-240da. This repair restores the published definitions and auxiliary constants,
and checks the broader manifest of importers and declaration users. It also
repairs stale provenance and overwritten lean.note fields as requested.

No false mathematical statement was found. The arbitrary-base class comparison
already supplies the canonical Chern arrow; no general detection of derived
maps by stalks is used. Both new mathematical obligations are genuine smaller
steps, with edge cases including the empty base, nonreduced bases, the zero
coefficient ring and N=1 accounted for in their proof descriptions.

## New nodes

lem-sp-finite-p1-diagonal-picard records the dual diagonal ideal's Picard identity.
lem-sp-ordinary-finite-chern-pullback records normalized Chern pullback naturality.
These are the only two new holes.

lem-sp-ordinary-finite-constant-unit-comp records the proved constant-unit pasting
law and the equality/composition interface for the unchanged supported unit.
def-sp-ordinary-finite-first-chern records the inverse of the proved class
bijection and its proved class, uniqueness and additivity API.
def-sp-ordinary-finite-coefficient-records records the canonical finite adjunction record and proved equations for the unchanged published
projective-line components. This repair node contains no hole.

Change records:

- coord/changes/F1-diagonal-alpha-instance-alignment.md
- coord/changes/F1-diagonal-supported-realization-interface.md
- coord/changes/F1-integral-class-lift-interface.md
- coord/changes/F1-ordinary-finite-coefficient-interface.md
- coord/changes/F1-supported-chern-instance-alignment.md
- coord/changes/F1-projective-diagonal-integrals-proof-witnesses.md

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer fix (efdbda997e1d)

The hole ordinaryFiniteChern_pullback is closed: the library already proves it
for arbitrary schemes as the private lemmas class_chern_pullback and
kummer_class_pullback of Sheaf.AlgebraicGeometry.FiniteP1ChernMapBaseChange
(lem-sp-finite-p1-chern-map-base-change). OrdinaryFiniteChernPullback now has the
proof import `import all Sheaf.AlgebraicGeometry.FiniteP1ChernMapBaseChange` and a
four-line proof; the statement is unchanged and `#print axioms` shows only propext,
Classical.choice and Quot.sound. The only hole this delivery leaves is
finiteP1_diagonal_picard (lem-sp-finite-p1-diagonal-picard). The node
lem-sp-ordinary-finite-chern-pullback records the proof. The item node's
proof_deps add lem-sp-ordinary-finite-chern-pullback (the proof uses its
ordinaryFiniteLinePullbackMap) and def-pc-divisor-line-bundle (isInvertible_dual_toModules).
The change record F1-diagonal-supported-realization-interface adds the six
omitted users of ordinaryFiniteP1DiagonalChartMap, among them
SfP1ChartMapComposition (held by H2).
