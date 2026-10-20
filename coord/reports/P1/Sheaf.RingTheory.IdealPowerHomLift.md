## What changed

Completed the listed retirement of `Sheaf.RingTheory.IdealPowerHomLift`.
`deleted.txt` withdraws the duplicate. Its only direct consumer,
`Sheaf.RingTheory.CyclicExtensionFlatDescent`, now privately imports
`WeilConjectures.RingTheory.IdealPowerHomLift`; its proof is unchanged.
The node `lem-weil-pbc-ideal-power-hom-lift` now points to the upstream theorem
`LinearMap.exists_ideal_power_hom_lift`, with its exact upstream signature.
The upstream theorem and its private Koszul helper already have complete proofs.
No upstream file, definition, target, mathematical statement, or unit route changed.
Change record: `coord/changes/retire-ideal-power-hom-lift-P1.md`.

## Proved and sorry left

Zero initial holes, zero closed, zero added, zero split off, zero remaining in the
item or adapted consumer. This is a duplicate retirement, not a new proof.
`LinearMap.exists_ideal_power_hom_lift` is supplied by the existing upstream proof.
The adapted cyclic consumer and its unchanged transitive consumer
`Sheaf.RingTheory.TorsionExtensionFlatDescent` compile against the replacement.
The delivery probe also checks allowed axioms. No new declarations are introduced.

## No longer needed

Pruned module: `Sheaf.RingTheory.IdealPowerHomLift`, including its duplicate
`LinearMap.exists_ideal_power_hom_lift` and private `exists_finite_koszul_cycle_lift`.
Removed the cyclic consumer's private import of that module and replaced it by
`WeilConjectures.RingTheory.IdealPowerHomLift`.
The retired module's three public Mathlib imports and six proof imports now live
only in the official implementation; none of the underlying mathematical
proof dependencies is pruned. No DAG node is deleted. The existing four-step
Koszul/torsion proof and all six proof-dependency nodes remain realized upstream.
Both downstream import closures change by exactly this one module replacement,
with no Sheaf/upstream twin pair introduced.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes an unproved obligation, but the current queue
marks this module `retire` with zero holes. The October 20 retirement hand-off is
the applicable work instruction. The node still pointed to the duplicate.
The retirement table reports restated declarations, but comparison shows only
hypothesis binder-name differences; positional use in the consumer needs no changes.
No mathematical defect was found. The required leanfinder, loogle and grep searches
were run through `msearch.py`; direct source search found the exact upstream theorem.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
