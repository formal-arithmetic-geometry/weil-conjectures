## What changed

Repaired the returned delivery against the current shared tree. The return at
52fcc0f4a6c identified an overlapping edit to
`Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative` after the old base
2f99cde02. Commit af62f65adee already consolidated that representative with its
adopted source implementation. Removed the stale representative copy from this
packet; the shared representative and its reviewed DAG record are preserved.
This is not a module withdrawal, and there is no `deleted.txt` entry.

The only delivered Lean change is
`Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchange`: replace its duplicate
local coefficient-map definition and exchange theorem with a public re-export
of the complete adopted source implementation. Its original public Sheaf
source-comparison and representative imports remain. Both original fully
qualified declarations remain available, with the same signatures and formulas.
The existing abbreviation `affineTildeFunctor = affinePushforwardTilde` makes
the entire old declaration section identical to the adopted source declaration
section after removing comments and whitespace.

No source-library file, target statement, other group's module, quarantine
archive, or DAG attachment changes. The source proof follows the existing node's
pre-normalization and counit-cancellation steps, so its dependencies and the unit
route remain unchanged.

Change record: `coord/changes/F4-affine-tilde-tensor-ordinary-exchange-rework.md`.

## Proved and sorry left

Zero-hole interface repair: the current item has 0 holes and the delivered item
has 0 holes. Holes closed: none. Holes added: none. Split off: none. No `sorry`
remains in the delivered file. `AlgebraicGeometry.affineTildeTensorOrdinaryExchange`
uses its complete existing source proof. No new proof or net hole reduction is
claimed.

Validation is repeated against the current shared representative. The retained
scratch checks restate the original coefficient target-map construction and
exchange signature, check the entire target-map function by `rfl`, restate both
representative constructions, check both entire functions by `rfl`, and apply
all three representative lemmas to their original signatures. Seven axiom
checks cover the two exchange declarations and five representative declarations.
The production interface compiles in 0.1 seconds; the ordinary and
representative compatibility checks compile in 35.9 and 39.8 seconds, with no
warnings. All seven checks report only `propext`, `Classical.choice`, and
`Quot.sound`. Scratch files are excluded from the delivery.

An additional full unchanged `AffineTildeDerivedTensorMate` compile reached the
60-second limit against the overlay. The separate baseline request has returned
transport timeouts rather than a Lean result while this packet was prepared.
No successful full-caller rebuild is claimed. The original exchange signature
and the entire target-map function used by that caller passed the focused
checks above; no caller statement or definition formula changes.

## No longer needed

The item's private import of
`WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility` and public
import of `Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization`
are supplied by the adopted exchange module. Its source publicly supplies the
same pre-normalization declaration and the chain comparison. The two existing
public Sheaf imports remain available.

The stale sandbox representative is no longer part of the delivery because its
consolidation already landed in af62f65adee. The library module is retained.
No DAG node or module is withdrawn or claimed globally pruned. The mate still
uses this exchange node; pre-normalization and chain nodes remain needed by the
source proof. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned packet overlapped E3's newer representative consolidation. This
repair uses that current version and removes the redundant proposed edit.

The historical route note predates the complete adopted source implementation.
That implementation now proves the exact equation and the entire split chain;
reusing it avoids another split and preserves the existing route. No
mathematical statement or proof step is disputed. The prior change record's
indirect user `AffineTildeDerivedTensorHomologyCoordinates` remains listed.
J3 has since restored that module as an adopted-source interface; its source
proof unfolds the unchanged adopted coefficient map.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
