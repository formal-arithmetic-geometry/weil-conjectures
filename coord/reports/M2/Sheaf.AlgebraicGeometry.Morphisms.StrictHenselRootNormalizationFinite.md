## What changed

Complete the approved retirement of
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite.
List its Lean file in deleted.txt and retain its mathematical DAG node, pointing to
WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite
with the exact current upstream declaration signature. Record the existing upstream
proof and structural-flatness dependency. No source-library or target file changes.

Reconcile the retained packet with current sources: its old tame-normalization
consumer is now an empty withdrawn module, and that consumer's node already names
the upstream twin. Preserve the obsolete consumer adaptation and parent-node copy
in scratchpad/prior-attempt-20261022; neither is delivered. The current upstream
parent already imports and applies the requested twin without an API adaptation.

Change record: coord/changes/M2-retire-strict-hensel-root-normalization-finite.md.

## Proved and sorry left

Zero-hole retirement: proved 0 of 0 sorries; closed none; added none; split off none.
No delivered Lean declaration contains sorry. The retained source theorem
AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_normalization_finite
has its existing complete proof. Its mathematical node and parent dependency remain.

## No longer needed

Pruned module:
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite.
Current Lean sources and quarantine have no importer of this copy. The sole DAG
parent, lem-sbc-strict-hensel-root-tame-normalization, is already attached to the
upstream tame-normalization module; that module imports and uses the upstream twin.
No mathematical node or blueprint unit step is pruned.

The retired small-colimit flatness reconstruction and comparison are unnecessary
in the retained full-colimit theorem. Its node now records
lem-sbc-affine-strict-henselization-structural-flat. The old direct dependencies
lem-weil-pbc-flat-ring-map-iff-ind-flat and lem-weil-pbc-etale-algebra-flat remain
available below that structural-flatness theorem. The small closed-fibre comparison
is no longer a dependency of this finiteness node. No other module is declared
unnecessary globally, and this delivery removes no import from a surviving source.

## Where the brief, the DAG or earlier work was wrong

This is an approved retirement with zero holes, not an unfinished proof assignment.
The earlier packet's consumer adaptation is stale: the Sheaf tame-normalization
module has since been withdrawn, its node moved to the upstream full-colimit
statement, and its downstream consumer adapted independently. Restoring that old
module or its DAG pointer would undo current work. There is no current rework row
or quarantine for the item. The current parent route is preserved unchanged.
The landed change record G8-retire-strict-hensel-root-normalization-generic-etale.md
confirms that consumer retirement and its downstream transport adaptation,
landing 20261021T173335-L-3588311.

The required first delivery check exited 143 without diagnostics or a DELIVERED
result, as in the preceding attempt. Reconciliation with current sources reduces
the packet to the approved withdrawal, its one node, this report, and the change
record. The delivery is retried only after that substantive packet repair.

Verification: a fresh scratch copy of the unchanged upstream tame-normalization
parent compiled through lcompile.py (10.9 seconds). A separate import-and-axiom
check compiled (1.6 seconds) and printed only propext, Classical.choice and
Quot.sound for both the finite-normalization and tame-normalization theorems.
No consumer of the retiring copy remains to adapt or compile.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
