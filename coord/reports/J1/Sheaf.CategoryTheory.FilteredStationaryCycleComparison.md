## What changed

Repaired the returned retirement delivery for `Sheaf.CategoryTheory.FilteredStationaryCycleComparison`.
The existing upstream twin supplies `CategoryTheory.filteredStationary_cycle_comparison`
with a byte-identical public signature. Restored the complete `FilteredPageTwoComparison` module and its DAG node required by the return; its proof remains hole-free. Replaced the private import in all three live
consumers: `Sheaf.CategoryTheory.FilteredPageTwoComparison`,
`Sheaf.Paper.EtaleCEStationaryPageNaturality`, and
`Sheaf.Paper.EtaleCEStationaryComparisonsAtBounds`. Their proofs and signatures are
unchanged. Listed the duplicate module in `deleted.txt` and repointed
`lem-weil-pbc-stationary-cycle-comparison` to the upstream module.

The upstream proof uses its proved private kernel-pullback helper instead of the
copy's direct Mathlib calculation. Updated proof step 3 and its dependencies to
record `lem-sp-derived-couple-kernel-identities`; the mathematical argument remains
actual-cycle coverage followed by comparison of two epic quotient maps with equal
kernels. No node, parent dependency or blueprint unit route is withdrawn.

All three adapted modules compile through `lcompile.py --all`: 8.1 s, 37.2 s and
24.3 s respectively. A separate server check of the upstream theorem reports only
`propext`, `Classical.choice` and `Quot.sound`. The original copy also compiled
before the retirement. Source-closure checks find no surviving direct import of
the copy and no pair of nonempty twins in the migrated consumer environments.
The change record lists all 18 downstream modules:
`coord/changes/retire-filtered-stationary-cycle-comparison-J1.md`.

## Proved and sorry left

This is a zero-hole duplicate retirement: proved 0 of 0 sorries; closed 0; added 0;
split off 0; left 0. The existing complete upstream proof of
`CategoryTheory.filteredStationary_cycle_comparison` is reused. The three consumer
modules also contain no `sorry`, and all their complete proofs are preserved.
This delivery claims pruning, not a new mathematical proof or a decomposition.

## No longer needed

Pruned module: `Sheaf.CategoryTheory.FilteredStationaryCycleComparison`.
Removed all three private imports of that module and replaced them with
`WeilConjectures.CategoryTheory.FilteredStationaryCycleComparison`.
Its duplicate private helpers and public comparison declaration are unnecessary;
the upstream twin already supplies the same theorem and representative equations.

No mathematical node is pruned. In particular,
`lem-weil-pbc-stationary-cycle-comparison` and every dependency already listed for
it remain needed through the upstream twin. The upstream derived-couple
kernel-pullback helper is also retained and now explicitly recorded in the node.
No source-library declaration or source-library import is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not describe this zero-hole item: the current queue
and `coord/retire-items.tsv` assign its retirement. The stated API difference
concerns only the private `filtered_class_preimage` helper, so it requires no
consumer proof changes. The actual public signatures agree exactly.

The retirement row lists two consumers; the live source has a third,
`Sheaf.CategoryTheory.FilteredPageTwoComparison`, which is adapted in the same
packet. None of the rework archives listed in `coord/rework.tsv` references the
copy. All quarantined modules and their attachments remain intact. No target
statement or mathematical definition changes.

## New nodes

Restored `lem-sp-filtered-page-two-comparison` and its complete `Sheaf.CategoryTheory.FilteredPageTwoComparison` module. The current base has no rework row or quarantine archive, so its metadata is attached to this J1 repair; the statement, proof and blueprint route are retained unchanged.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
