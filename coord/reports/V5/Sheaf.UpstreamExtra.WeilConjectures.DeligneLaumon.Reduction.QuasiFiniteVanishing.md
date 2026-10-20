## What changed

Restored the quarantined module
`Sheaf.UpstreamExtra.WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing`
to its original Lean path. Removed the dangling
`attribute [local instance] Compactification.over in` immediately before
`end LowerShriek`: its associated theorem was removed by upstream synchronization,
so the scoped command was incorrectly consuming the section terminator.
All five private declarations, their signatures and proofs, and all imports are preserved.
Wrapped the generated module comment and disabled `linter.privateModule` because
this synchronization companion intentionally contains only private helpers.
No upstream source file is changed.

For the returned delivery `d2842da8b` (base `aacbf8401`), re-read the current
return and rework row and reconstructed this module from the current quarantine
archive. The active library path remains absent in the current shared tree;
the archive still contains the invalid scoped command. The returned version's
five private declarations and imports agree with this reconstructed repair.
Restoration therefore reapplies the actual parsing repair to the current assigned
source, rather than withdrawing the archive or replacing it with an empty module.
No independently changed declaration or import is overwritten.

The repaired module compiled through `lcompile.py` with exit code 0 and no warnings.

Change record: `coord/changes/V5-quasi-finite-vanishing-companion-scope.md`.

## Proved and sorry left

This is the rework repair listed in `coord/rework.tsv`, not a proof item.
Actual holes before: 0. Actual holes after: 0. Holes closed: none. Holes added: none.
No split-off statements. The retained private definition `wContractibleAffine` and
four private theorems already have complete bodies, which are preserved verbatim.
Single-file compilation verifies the repaired scope and all retained proof bodies.

## No longer needed

Only the orphaned scoped attribute command is removed. No imports, declarations,
DAG nodes, or modules are pruned. No new proof dependency is introduced.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a module containing `sorry`, but the actual assigned
item is a zero-hole synchronization rework repair. Its source is in
`quarantine/Sheaf/UpstreamExtra/WeilConjectures/DeligneLaumon/Reduction/QuasiFiniteVanishing.lean`,
not at its original active library path. `coord/rework.tsv` records the original
compiler error: `Unexpected name LowerShriek after end: The current section is unnamed`.
The extraction retained the scoped attribute while removing the theorem to which
it applied. There is no DAG node whose Lean record names this companion and no
active or quarantined consumer imports it. No statement or mathematical route changes.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
