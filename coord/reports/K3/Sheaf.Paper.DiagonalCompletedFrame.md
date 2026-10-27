## What changed

Replaced the body of `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCompleted_frame`
by a complete assembly proof. The original statement and every existing definition stay
unchanged. Added private proof imports of `CompletedCoefficientRealization`,
`CompletedCoefficientOrdinarySquare`, `CompletedSupportedCoefficientTransport`, and the
already proved `DiagonalIntegralRootMap`.

The proof maps the global-section unit condition to the projective line and its product,
obtains three coefficient realizations, and uses integral-root uniqueness to match all
three specified root maps. It obtains ordinary squares for the three projections and the
diagonal. The supported-source isomorphism is constructed explicitly from the ordinary
diagonal square and the regular-unit comparison; supported-source transport is applied
separately to both projections before constructing `CompletedFrame`.

The underlying-sheaf normalization of this constructed supported isomorphism is also
proved directly in `completedSupportedCoefficientIso_normalization`, by cancelling the
underlying regular-module comparison in the ordinary diagonal square equation.
Proved private categorical cancellation helpers and a named equality for the underlying
supported source keep this calculation from repeatedly unfolding the concrete sheaf and
completed-module definitions during checking. The result stays heterogeneous, as required
by the existing normalization field; no shared unfolding behavior is changed.

Validation: the final four Lean files all compile through `lcompile.py` and also through
the compile phase of `deliver3.py`. The optimized standalone source-normalization test
completed in 16.8 seconds. No delivered file emits a warning. The delivery did not push:
the tool's warning gate includes cached diagnostics of an unpublished external dependency
(see below).

The three new modules isolate the three construction steps of the existing node's plan.
None is a renaming or repackaging of the frame: the first concerns one coefficient category,
the second one ordinary morphism without derived data, and the third assumes all
realizations and ordinary squares and concerns only supported-source transport. No trace,
diagonal class, or integration equation is asserted by these intermediate statements.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCompleted_frame`
(node `lem-diagonal-completed-frame`) by decomposition, not an independent proof of all its
coefficient theory. The item module has zero remaining holes, compared with one before.

Also proved
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedSupportedCoefficientIso_normalization`
(node `lem-diagonal-completed-supported-transport`).

Added exactly three whole-theorem holes:

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedCoefficientRealization_exists`
  (`lem-diagonal-completed-coefficient-realization`).
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedCoefficientOrdinarySquare_exists`
  (`lem-diagonal-completed-ordinary-square`).
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedSupportedCoefficient_transport`
  (`lem-diagonal-completed-supported-transport`).

Thus one original hole is closed and three strictly smaller holes are added: this is a
three-part decomposition, with no claim of positive net sorry progress. The supported
coefficient isomorphism is an actual definition, using only the given ordinary square and
unit isomorphism. No definition contains `sorry` or selects arbitrary data from an
unproved existence theorem.

## No longer needed

No import, module, or node is withdrawn. The old direct coefficient-limit and pullback
proof dependencies are used by the new one-scheme realization and ordinary-square nodes,
so they remain needed indirectly. The existing derived-square theorem and canonical
derived models remain in use. A separate proof of condensed supported-source acyclicity
using exact closed-immersion direct image is unnecessary: transport preserves the
acyclicity already supplied by the input `SupportedSource`. The old plan attached no
separate named node or import to that argument, so no module is pruned globally.

## Where the brief, the DAG or earlier work was wrong

Delivery tool failure: `deliver3.py K3 Sheaf.Paper.DiagonalCompletedFrame` reports
`COMPILES WITH WARNINGS (local), nothing pushed`, although all four delivered modules have
status `compiled`. Every warning is from the automatically compiled unpublished dependency
`Sheaf.AlgebraicGeometry.SfP1ChartExchange`, lines 565-566: unused simp arguments
`ordinaryFinitePullback`, `ordinaryFiniteLine`, and `ordinaryFiniteDegreeZero`. Those cached
dependency diagnostics are attributed to this packet's warning gate. The packet does not
change that module or cause those warnings. No delivery tool was patched or bypassed.

Resumed attempt (2026-10-26T16:21:29+00:00): started with the required
`deliver3.py K3 Sheaf.Paper.DiagonalCompletedFrame` check. It again exited 1 at
`COMPILES WITH WARNINGS (local), nothing pushed`, with all four packet modules
reported as `compiled`. The warnings still refer to the cached unpublished
`SfP1ChartExchange` dependency from commit
`c0c6c1dbd53a01ace3cacf8b04fe35c4221e2554`. The current shared source already
removes the three unused arguments from the simp call at lines 565 onwards;
the cached diagnostics therefore do not describe that current source.
`coord/claims/Sheaf.AlgebraicGeometry.SfP1ChartExchange.lock` still names B2.
Read-only inspection of `deliver3.py` confirms its local warning check scans
all compile output, including these dependency messages. No documented cache
refresh option is provided by `lcompile.py --help`. The retained Lean packet,
node files, and hole counts are unchanged; no cache, launcher script, shared
source, or another group's module was altered to evade the gate.

The original plan's third step named no dependency for constructing and transporting the
normalized supported source. Its missing coefficient construction steps are now explicit
Lean statements with separate nodes and complete source-based proof plans. The original
frame signature was usable without weakening any hypothesis or conclusion. The unit's
statement and route are unchanged; its `realized` fields currently contain no node that
this proof bypasses.

The item and its dependencies were briefly absent from `lean/` during synchronization.
The archive and rework row were read before restoration; the shared source subsequently
returned unchanged. No quarantined path is withdrawn by this delivery.

The new statements were checked on empty schemes, identity morphisms, arbitrary normalized
input realizations, and arbitrary supplied acyclic supported sources. In particular the
last statement uses the given source's acyclicity; it does not assume every module is
acyclic. LeanSearch, LeanFinder/Loogle and local library/Mathlib searches found general
scalar, single-complex, and exact-derived APIs, but no complete normalized construction.

## New nodes

`lem-diagonal-completed-coefficient-realization` supplies one exact coefficient realization
with its regular and root-line normalizations. Its source is the integral coefficient
identification, and it keeps the existing internal/sectionwise equivalence and normalized
integral-limit dependencies.

`lem-diagonal-completed-ordinary-square` supplies an ordinary normalized direct-image
square for any morphism and supplied realizations. It isolates linearity and naturality
from the already proved right-derived-square construction.

`lem-diagonal-completed-supported-transport` constructs the supported-source isomorphism
from the ordinary diagonal square and transports a single normalized acyclic supported
source through any supplied ordinary projection square. It is reused for both projections.
No existing shared interface changes, so no change record or forced adaptation is needed.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
