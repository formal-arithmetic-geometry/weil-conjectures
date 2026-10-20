## What changed

Completed the listed retirement of `Sheaf.RingTheory.CyclicExtensionFlatDescent`.
The sole direct consumer, `Sheaf.RingTheory.TorsionExtensionFlatDescent`, now privately
imports `WeilConjectures.RingTheory.CyclicExtensionFlatDescent`. Its theorem signature
and proof are unchanged. `deleted.txt` withdraws the duplicate module. The node
`lem-weil-pbc-cyclic-extension-flat-descent` now points to the complete upstream
`LinearMap.exists_cyclic_extension_flat_descent`, with its exact upstream signature.
Change record: `coord/changes/retire-cyclic-extension-flat-descent-N2.md`.

The upstream theorem has the same hypotheses and conclusion: only hypothesis binder
names differ. The positional application in the consumer requires no proof change.
The upstream proof constructs the graph quotient explicitly and establishes both
comparison squares and bijectivity; the upstream ideal-Hom lifting theorem is also
proved. The five DAG proof steps and all mathematical dependencies stay unchanged.
No upstream source, definition, target statement, public import or unit route changes.

## Proved and sorry left

Zero initial holes, zero holes closed, zero holes added, zero split off, zero remaining
in the retired item or adapted consumer. This is a duplicate retirement, not a new proof.
`LinearMap.exists_cyclic_extension_flat_descent` is supplied by the existing complete
upstream proof. The original item compiled in 4.0 seconds; the adapted sole consumer
compiled without warnings in 7.1 seconds. The delivery tool also probes allowed axioms.
No new declaration is introduced.

## No longer needed

Pruned module: `Sheaf.RingTheory.CyclicExtensionFlatDescent`, containing the duplicate
`LinearMap.exists_cyclic_extension_flat_descent`. Replaced its sole consumer's private
import by `WeilConjectures.RingTheory.CyclicExtensionFlatDescent`.
The duplicate's three public Mathlib imports and its two private imports are retained
by the upstream implementation, so no mathematical dependency is pruned.
The consumer's import closure removes exactly the Sheaf copy and adds exactly the
upstream twin (29 modules including Mathlib boundary imports); no Sheaf/upstream twin
pair occurs before or after this change. The already-retired ideal-Hom copy stays retired.

The only DAG parent is `lem-weil-pbc-torsion-extension-flat-descent`; it continues to
use the same node and theorem via the new attachment. No node, unit statement or unit
proof step is removed. Search across Lean sources, quarantined sources and node files
found no other import or attachment to migrate. The ideal-Hom node's `created.item`
field is historical provenance, not a current dependency, and remains unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an unproved obligation, but `coord/queue.tsv` and
`coord/retire-items.tsv` mark this as a retirement with zero holes. The October 20
human retirement instruction applies. The kept-twins table reports a restatement;
comparison shows only binder-name differences, and the consumer compiles unchanged
apart from its private import. The DAG attachment still pointed to the duplicate.

No mathematical defect was found. Required leanfinder, loogle and grep searches were
run through `msearch.py`; the exact proved match was found by direct library search.
No second worker was started; the maintainer's independent review remains the review.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
