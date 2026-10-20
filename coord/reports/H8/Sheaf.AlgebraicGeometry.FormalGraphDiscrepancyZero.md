## What changed

Restored the current quarantined source of
`Sheaf.AlgebraicGeometry.FormalGraphDiscrepancyZero` and added
`public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule` before its
existing proof imports. The archive's copyright, documentation, declarations,
proofs, and private proof imports are preserved verbatim. This repairs the
recorded unknown-`Scheme` error: the types used by the public theorem must be
publicly imported. No definition, theorem signature, or source-library file changes.
Change record: `coord/changes/H8-formal-graph-discrepancy-public-import.md`.

For the return at `65373411d1`, compared the retained packet with the current
shared source and `coord/rework.tsv`. The active source is absent; its current
source is preserved at
`quarantine/Sheaf/AlgebraicGeometry/FormalGraphDiscrepancyZero.lean`.
Rebuilt this packet from that archive, rather than resubmitting the previous
packet's alternative proof. The restored module compiles cleanly through
`lcompile.py` in 4.1 seconds. A separate importing probe also compiled,
confirmed public visibility of `Scheme` and the theorem, and printed exactly
`[propext, Classical.choice, Quot.sound]` as the theorem's axioms. The archived
`FormalGraphFirstQuotientEpi` consumer compiled unchanged against the restored
module in 3.7 seconds as a scratch probe.

The existing DAG attachment and both proof dependencies remain valid. The proof
establishes uniform quotient annihilation, computes the discrepancy at level n,
and propagates zero to every level by stabilization and epimorphic transitions.
The fixed unit route is preserved.

## Proved and sorry left

`AlgebraicGeometry.formalGraph_discrepancy_zero` and the private helper
`formal_zero_of_level` are fully proved in the restored archive. This is an
import-visibility repair with zero existing holes, zero holes closed, zero holes
added, zero holes remaining, and zero split-off obligations. No new mathematical
claim is counted as proved by this repair.

## No longer needed

None. No imports, modules, declarations, or DAG dependencies are removed.
The completion module provides the statement and annihilation lemmas; the kernel
factorization module provides `formalTransition_epi`. Both remain necessary.

## Where the brief, the DAG or earlier work was wrong

The returned delivery conflicted with an intervening source change. The current
rework row identifies the authoritative quarantined file and its public-import
failure. The earlier retained report described restoring a rewritten proof;
this repair instead preserves the current archived proof exactly and fixes its
missing public import. The existing node accurately describes that proof and
requires no changes. No definition repair or consumer adaptation is necessary.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
