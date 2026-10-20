## What changed

Restored Sheaf.Paper.PbcUniformLocalModelCohomology from the quarantine path assigned
in coord/rework.tsv. Replaced three occurrences of the retired
LocallyClosedStratification name with Scheme.Stratification: in the private
uniform_upper and uniform_constructible helper signatures, and the local hcanonical
assertion. All proofs, the public theorem signature and all imports are preserved.

The original archive fails with unknown-identifier errors at lines 68, 223 and 316
and a cascading unsolved goal. The repaired complete file compiles cleanly through
lcompile.py in 10.5 seconds. No resource limits or library definitions were changed.
The existing node attachment, proof plan and dependencies still describe the restored
proof exactly, so no node edit is needed.

Change record: coord/changes/C4-uniform-local-model-stratification-rework.md.

## Proved and sorry left

This is a zero-hole rework repair, not a new hole closure. The archive contains zero
sorry proofs, and the repaired module contains zero. Holes closed: none (0 of 0).
Holes added: none. Split off: none. There are no remaining sorry declarations in the
delivery. AlgebraicGeometry.Scheme.pbcUniformLocalModelCohomology is restored with its
complete archived proof from the existing dependency declarations.

## No longer needed

None. All five imports are used by the restored statement or proof. No node, module
or declaration is withdrawn. The parent lem-weil-pbc-uniform-reduction-criterion
continues to need this theorem, including its quarantined consumer module.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because of its recorded quarantine, rather than because
it was withdrawn. Its preserved proof has zero holes. The archive refers to the retired
LocallyClosedStratification type, while the current tower predicate, stratum detection
and repaired levelwise truncation theorem all use Scheme.Stratification. The latter's
constructibility condition is automatic under the existing Noetherian hypothesis;
no mathematical hypothesis or conclusion is weakened or strengthened here.

The current return file has no item-specific numbered return. The existing unit route
and every node dependency are retained. Searches with leanfinder, loogle and grep found
no replacement theorem for this assertion; the existing complete proof is reused.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
