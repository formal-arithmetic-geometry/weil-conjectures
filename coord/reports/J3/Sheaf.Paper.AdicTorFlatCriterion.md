## What changed

Restored the quarantined `Sheaf.Paper.AdicTorFlatCriterion` source after the merge-queue
cluster restore. The module compiles against the current library and preserves the target
statement and its documented proof plan.

## Proved and sorry left

No theorem hole was closed. The existing theorem `pbc_adic_tor_implies_flat_cohomology`
remains `sorry`; this is a rework restoration listed in `coord/rework.tsv`.

## No longer needed

No imports, nodes, or modules were pruned. The attempted quarantined characterization
module was not used and is absent from the delivery.

## Where the brief, the DAG or earlier work was wrong

The quarantined proof dependencies include a retired `LocallyClosedStratification`
interface, while the current active tower interface uses `Stratification`; that dependency
cannot be restored as a proof import without a broader cluster repair. The target module
itself remains independently compilable with its original imports.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
