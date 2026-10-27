## What changed

The fixed-true transport equation keeps its original signature. Its proof uses a generic
naturality-pasting lemma, the normalized coefficient-coordinate square, the constant-unit
composition equation, and a coefficient-independent presentation-exchange equation.

An explicit equality of the two second-projection functors transports both sides of
the Boolean interface. The proof cancels its component before the categorical pasting
calculation.

The coefficient-coordinate square is proved in
`Sheaf.AlgebraicGeometry.SfP1CoordinateLineComparison`. Its private argument establishes
composition of normalized finite Tate transport, transports that equation through exact
degree zero and the canonical left-derived comparison, and then shifts by two. The case
N = 0 is handled using emptiness forced by invertibility of zero. The square calculation
then cancels the normalized line isomorphisms. These helpers follow the proved private
comparison argument in SfP1ChartExchange; that private API cannot be imported directly.

The unit calculation recovers the constant-unit square from the existing proved cached
right-unit compatibility theorem. Tensoring by the pullback of the actual constant unit
is faithful, because it is isomorphic to the tensor unit. Naturality, canonical right
unitality, and cancellation therefore identify the two unit maps. The normalization of
the actual constant object and of its right unitor are proved separately. This route
avoids normalizing the entire cached degree-zero pullback functor.

The trace construction in the shared SfP1IntegralTransportData module is factored
through the real coefficient-independent presentationTrace construction and the
polymorphic traceComposite composition. Its proved
presentationTrace_assoc equation recovers the previous order of factors by
associativity. The proper forget-supports and inverse line comparison remain in
their original order. This repairs a kernel-normalization slowdown at the concrete
shifted line. Existing signatures, attributes and instances are preserved. This repair
restores the current main public import of SfP1SupportedExtMapData and removes the
stale duplicate supportedMap from the data module. Its declaration and node attachment
remain in SfP1SupportedExtMapData, and the data node retains that statement dependency.
The change is recorded in coord/changes/sf-p1-trace-factorization.md. The quarantined
item was read and preserved, and its statement has not been withdrawn.

## Proved and sorry left

Actual module hole counts: SfP1ProjectionTraceTransportTrue 0,
SfP1IntegralTransportData 0, ProjectiveLineTraceNormalization 0,
SfP1PresentationExchange 1, and each other new module 0. The repair itself adds no hole.

The original hole in
`AlgebraicGeometry.Etale.SfP1Transport.projectionTraceTransport_true` is replaced by a
complete combining proof. This is a decomposition: one original hole is closed and one
new hole is added, so it is not reported as a net proof of the original obligation.

The new hole is
`AlgebraicGeometry.Etale.SfP1Transport.presentationExchange`, node
`lem-sf-p1-presentation-exchange`. It is the exchange-pasting identity for an arbitrary
complex before inserting a coefficient comparison, a trace arrow, or a constant-unit
comparison. Its statement contains none of N, hA, t, hS, or tau. It is a geometric part of
the original calculation, rather than the original conclusion under another name.

`AlgebraicGeometry.Etale.SfP1Transport.coordinateLineComparison` is proved without any
new hole. The generic pasting proof and the constant-unit calculation also have complete
proofs. The new declarations constantUnit_eq_single, cachedRightUnit_eq, and
constantUnit_pullback are fully proved; their modules have zero holes. No sorry remains
inside a definition or a private theorem. The new shared theorem
AlgebraicGeometry.Etale.SfP1Transport.presentationTrace_assoc is also fully proved.

## No longer needed

No original import is removed: SfP1ChartExchange is still required by the statement.
The planned dependency `lem-sfb-ringed-derived-monoidal-comparisons` and its abstract
comparison system are not used on this route. The concrete canonical single-degree and
unit comparisons from the source library are used instead. Proper finite-coefficient
base change remains necessary for the exchange maps; twist uniqueness and finite twist
pullback remain necessary for the proved coefficient lemma. No module is withdrawn and
no blueprint unit or its realized proof route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original expanded trace definition was too expensive
to normalize in the concrete pasting proof. The shared definition repair factors it
at an arbitrary complex and proves compatibility with the old formula.

Return A1/H4: the returned packet 1473a6fb335 used a stale base. It missed A4's separation of
supportedMap into SfP1SupportedExtMapData and D3's new normalization consumer.
The data module and its node are now rebased onto current main: its public import,
statement dependency def-sf-p1-supported-ext-map-data, and declaration ownership are
restored. The earlier report's claim of four direct importers was incorrect: current
main has nine. They are SfP1ChartMapComposition, SfP1ChartExchange,
SfP1IntegralTraceComparison, SfP1IntegralSectionComparison,
ProjectiveLineTraceRawAdjustment, ProjectiveLinePresentedKernelAdjunction,
ProjectiveLinePresentedKernelIntegrals, ProjectiveLinePresentedIntegrals, and
ProjectiveLineTraceNormalization. The normalization proof requires the forced
adaptation described below. All 19 validation modules compiled successfully: the nine
packet modules, all nine
current direct importers (normalization overlaps the packet), ProjectiveLineTraceAdjunction,
and the unchanged parent SfP1ProjectionTraceTransport. The ten unchanged validation
copies were removed after checking; the forced normalization adaptation remains.

The declared dependencies give the canonical maps, proper
exchange invertibility, and normalized twist transport. They do not directly state the
mixed comparison equation with the chosen pushPull. The new presentation-exchange node
isolates that specific step. The coefficient and unit calculations are carried out rather
than passed to another copy of the full transport equation.

## Forced adaptations

Return 2b: Sheaf.SixFunctors.ProjectiveLineTraceNormalization is unclaimed. Reviewer C-1473a
reported that its original traceProofCongruence fails against the repaired data module:
unfolding trace reaches traceComposite and produces "non-proof disagreement". The
original module compiles on main, so the change is forced by this packet's trace body.

In ProjectiveLineTraceNormalization.lean, lines 30-32 extend the private
unfoldInstanceBoundary whitelist to recognize traceComposite. Lines 181-183 add the
associativity rewrite. Before
structural congruence, the public theorem's proof folds the adjacent direct-image
composition and cancellation factors with the proved presentationTrace_assoc equation.
This supplies the grouping used by the new trace body without a concrete definitional
bridge. Every existing public signature, visibility, attribute, public import and
docstring in this module is unchanged. No new hole is introduced. The downstream
ProjectiveLineTraceAdjunction is included in the repair validation.

The existing normalization node is updated only in its proof and proof origin to record
the associativity step; its statement and dependencies stay unchanged.

The adaptation is recorded in
coord/changes/sf-p1-trace-normalization-adaptation.md; the data repair and its current
importer list are in coord/changes/sf-p1-trace-factorization.md.

## New nodes

`lem-sf-p1-presentation-exchange` records the remaining exchange-pasting step, with its
source paragraph and a proof in words describing proper forget-supports compatibility,
ordinary base-change pasting, and inverse-image/direct-image cancellation along i.

`lem-sf-p1-coordinate-line-comparison` records the proved inverse-image-only coefficient
square. It also attaches the proved first-projection-square wrapper used by the exchange
statement. These statements retain empty schemes and zero coefficient rings.

`lem-sf-p1-constant-unit-normalization` identifies the constructed constant-unit
isomorphism with the canonical degree-zero unit isomorphism.

`lem-sf-p1-cached-right-unit-normalization` identifies the constructed constant-object
right unitor with the existing single-object right unitor.

`lem-sf-p1-constant-unit-pullback` records the proved unit square obtained by faithful
tensor cancellation. These three nodes contain no holes.

`lem-sf-p1-trace-transport-pasting` records the fully proved generic categorical
calculation in a separate module to keep the concrete file small. It adds no hole.

The shared trace-factorization repair and its proved associativity equation are attached
to def-sf-p1-integral-transport-data. The change record is
coord/changes/sf-p1-trace-factorization.md.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
