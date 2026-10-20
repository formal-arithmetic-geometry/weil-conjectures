## What changed

Completed the queue's retirement item for
Sheaf.AlgebraicGeometry.ProEtale.RepleteOnContractible.
The existing source-library theorem has a byte-identical signature and proof.
Redirected the sole consumer, Sheaf.AlgebraicGeometry.ProEtaleReplete, to
WeilConjectures.AlgebraicGeometry.ProEtale.RepleteOnContractible by changing
one private import. Withdrew the duplicate via deleted.txt and reattached
DAG node det-pe-replete-on-contractible to the existing source declaration.
No upstream file or target statement changes.

Change record: coord/changes/replete-on-contractible-retirement.md.
The source theorem's proof and the blueprint unit's route are preserved.
The consumer still explicitly imports SiteCoveringAxioms, which the duplicate
also exported. Its new import closure contains no twin-module clashes, and
import_direction.py accepts the replacement.
Server lcompile.py compiled the adapted consumer cleanly in 1.9 seconds.
A separate source-theorem axiom probe compiled in 1.6 seconds and reported
only propext, Classical.choice, and Quot.sound.

## Proved and sorry left

Zero original holes; zero holes closed, zero added, and zero split off.
AlgebraicGeometry.Scheme.proetale_surjective_sections_of_epi_tower is retained
with its complete existing proof in the source library. There are no remaining
sorry declarations in the retired item or the adapted consumer.
This is a retirement, not a newly proved theorem or a decomposition.

## No longer needed

Retired module: Sheaf.AlgebraicGeometry.ProEtale.RepleteOnContractible.
Removed its sole import in Sheaf.AlgebraicGeometry.ProEtaleReplete, replacing
it with the source twin. The duplicate's Lean implementation is no longer
needed; its DAG node and mathematical statement remain needed and now point
at the adopted source module. No mathematical proof dependencies are pruned:
weak contractibility, epi/local surjectivity, and sectionwise limits remain
used in the retained proof. No other modules or nodes are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module with holes or a repair. The queue
and coord/retire-items.tsv identify this specific assignment as retirement:
its theorem was already proved, and the adopted source tree contains the
identical proof. The DAG still pointed at the duplicate. This delivery corrects
that attachment and removes the duplicate without changing the mathematics.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
