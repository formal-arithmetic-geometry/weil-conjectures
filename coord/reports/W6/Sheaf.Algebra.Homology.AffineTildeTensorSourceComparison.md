## What changed

Restored the quarantined `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison`
as a compatibility interface for the complete adopted source implementation.
Its original public core-final import is retained and the adopted comparison
module is publicly imported. The original fully qualified comparison theorem,
its isomorphism and universal counit transport equation are available unchanged,
using the existing definitional equality of the two affine tilde abbreviations.
The archive and source-library declarations are untouched.

The archived module fails at its universe-sensitive local abelian instance.
The adopted implementation explicitly supplies the sheaf universe and already
contains the entire archived theorem and proof, identical after substituting
`affineTildeFunctor` by `affinePushforwardTilde` and normalizing whitespace.
Re-exporting this implementation repairs the failure and avoids a duplicate
public theorem. Change record:
`coord/changes/W6-affine-tilde-tensor-source-comparison-rework.md`.

Validation: the restored interface compiles cleanly (1.8 seconds). Two scratch
consumer checks compile the verbatim archived statement by applying the source
theorem (21.3 seconds) and the archived theorem proof against the restored core
API (44.0 seconds), with fresh local instance names and the corrected explicit
sheaf universe. All three checked theorems have only `propext`, `Classical.choice`,
and `Quot.sound` as axioms. The added import passes the import-direction check.
Scratch checks are not delivered as library modules.

## Proved and sorry left

This is the assigned zero-hole quarantine repair. The archived module has zero
`sorry`s and the restored module has zero. Holes closed: none (0). Holes added:
none (0). Split off: none (0). No named theorem is left with `sorry`.
The complete adopted `AlgebraicGeometry.exists_affineTildeTensorSourceComparison`
proof is re-exported, not replaced by a new obligation or new chosen data.

## No longer needed

No public import, node, dependency or module is removed or withdrawn. The restored
path remains available to all four quarantined direct Sheaf consumers. The
original K-flat/precomparison and affine pushforward routes remain needed and
are supplied by the complete adopted source implementation. No new node is
needed and no unit route is bypassed. The duplicate local instance declarations
and theorem body are supplied by the adopted implementation.

## Where the brief, the DAG or earlier work was wrong

The current item is an explicit compilation rework with zero holes, rather than
a remaining unproved source comparison. The route note predates consolidation
of the core-final, precomparison, prebase and normalization interfaces. The
current adopted library contains the exact comparison and its complete proof;
no additional split, root bypass or affine-core restructuring is necessary.

The archived source was inspected under its `coord/rework.tsv` entry; its absence
from `lean/` is not treated as withdrawal. The node retains its existing Lean
attachment and all dependencies because the same mathematical proof is reused.
The four quarantined direct consumers are listed in the change record and their
interfaces are preserved. The current W6 return concerns a different item whose
landing was blocked by this missing path; this packet restores the missing
path without modifying that unrelated module.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
