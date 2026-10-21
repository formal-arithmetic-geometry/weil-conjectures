## What changed

Restored the complete quarantined module
`Sheaf.AlgebraicGeometry.PicardKunnethQcohFunctoriality` from the archive named
in coord/rework.tsv. Replaced its stale public import of the withdrawn empty
Sheaf scalar-operations module with
`WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`, which
exports the vocabulary required by the public statement. The archived theorem
signature, proof body, visibility, docstrings and all other imports are verbatim.
No adopted source file was edited.

The proof unfolds the external cup and its coefficient comparison, applies
`scalarCup_pullback_coefficient_naturality`, then applies
`scalarCohomologyPullback_square` to each projection. Both existing scalar
compatibility modules are used. The node's proof and dependency lists already
record this argument; only its Lean note records restoration. The unit route is
unchanged. Change record:
`coord/changes/picard-kunneth-functoriality-upstream-import-K2.md`.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.picard_kunneth_functoriality`
(node `lem-sc-picard-kunneth-qcoh-functoriality`) retains its complete proof.
This is a zero-hole quarantine repair: 0 original sorries, 0 holes closed,
0 holes added, 0 split off, and 0 remaining in the delivered module.
No new declarations or proof obligations were introduced.

The corrected module compiles cleanly with lcompile.py (8.7 seconds in the repeat
check). An independent scratch `#print axioms` probe reports exactly propext,
Classical.choice and Quot.sound. A validation-only copy of the sole archived
parent PicardKunnethQcoh, correcting its independent stale operations import,
compiles against the restored artifact in 3.8 seconds. That copy is outside the
delivered Lean tree; its separate rework is not claimed completed here.

## No longer needed

Removed the public import of the empty withdrawn module
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`, replacing it
with the canonical upstream operations. No mathematical nodes or modules are
pruned. Both scalar compatibility proof imports remain necessary and are retained.

LeanFinder returned scheme pullback-cover identities, none stating scalar
external-cup naturality. Loogle confirms pullback.condition, already used in the
proof. msearch grep found no external-cup pullback duplicate; direct scans of both
library roots and quarantine find the existing archived theorem and its sole
parent application. The accepted short scalar argument is preserved.

## Where the brief, the DAG or earlier work was wrong

The assigned module is quarantined, not withdrawn, and its archive already has
zero sorries. Its public operations import had not followed retirement of the
duplicate Sheaf operations module. The original archive fails with unknown scalar
cohomology and cup identifiers; Lean requests the canonical public upstream
import. Correcting that import restores compilation without altering any theorem
or definition. The DAG attachment and proof dependencies are preserved.

`tools/downstream.py` cannot index the quarantined module; scanning both source
and quarantine finds the sole direct consumer PicardKunnethQcoh. It has its own
independent stale public import, so it remains a separate rework item. The current
item has no return entry requiring a different proof or withdrawal.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
