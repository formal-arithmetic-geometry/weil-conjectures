## What changed

Restored lean/Sheaf/CategoryTheory/CoefficientFiniteLocalSystemsPullback.lean verbatim
from the quarantine path specified by coord/rework.tsv. The active source was absent
following the cluster restore. This is a source restoration, not a theorem withdrawal
or a rebase-only repair. The complete existing proof, private comparison constructions,
public import and theorem signature are preserved. No source-library file changes.

Reviewed the proof against its three DAG steps: product-preservation and adjunction
mates give the restriction comparison; a terminal-object trivializing covering sieve
pushes forward and pulls back to a target cover; localized inverse image and further
restriction preserve the same constant module M and its finite-generation proof.
Empty covering sieves remain valid, and no finiteness of the underlying coefficient
set or Noetherian hypothesis is introduced.

The module compiled cleanly through lcompile.py (6.5 seconds, and 10.7 seconds in the
consumer check). A separate #print axioms compile (6.9 seconds) reported exactly
propext, Classical.choice and Quot.sound. The temporary probe was removed.

Change record: coord/changes/K2-restore-coefficient-finite-local-systems-pullback.md.
The unchanged quarantined consumer NoetherianGlobalConstructibility was also submitted
to lcompile.py with the restored module. It stopped at its first import: the published
object file for CoefficientAffineConstructibleProEtaleModules is absent. This separate
quarantine dependency prevents a full consumer compile; the consumer's two theorem
applications were read and use the preserved signature. No consumer is changed here.

## Proved and sorry left

The restored theorem CategoryTheory.coefficient_finite_local_systems_pullback is fully
proved and has only the three permitted axioms. Its node remains
lem-sfb-coefficient-finite-local-systems-pullback.
The archive had zero holes; the restored module has zero holes. Holes closed: zero.
Holes added: zero. No declarations are split off and no sorry remains in the delivery.
This delivery does not claim a new proof of the already proved archived theorem.

## No longer needed

None. No imports, nodes or modules are pruned. Both declared proof dependencies remain:
def-pe-etale-constructible-module (the local-model predicate) and
def-weil-pbc-constant-sheaf (constant sheaves). The quarantined parent still needs this
module. The node, its Lean attachment, proof steps and proof_deps remain unchanged.
Searches using leanfinder, loogle and grep found no direct replacement for the predicate
preservation theorem; the existing constant-sheaf comparison is already used.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole quarantine restoration. Its missing active source does not
indicate unused mathematics: the archived parent still imports and applies it twice.
No mathematical error or statement change was found. The unit route is retained.
The consumer compilation limitation above concerns a separately absent published
quarantine dependency, not this restored proof.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
