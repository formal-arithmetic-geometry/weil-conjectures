## What changed

Withdraw `lean/Sheaf/RingTheory/PowerSeriesRingSubfields.lean` using `deleted.txt`, following
the human-authorized retirement instructions in
`coord/changes/retire-sheaf-twins-20261020.md` and its item in `coord/retire-items.tsv`.
Repoint `lem-weil-pbc-power-series-ring-subfields` to the existing upstream declaration
`RingTheory.iInter_frobenius_subfields_mvPolynomial_mvPowerSeries` in
`WeilConjectures.RingTheory.PowerSeriesRingSubfields`; update the recorded statement's name.
The theorem signature and complete proof body are textually identical after renaming.
The unit route and all mathematical statements remain unchanged.

No current module imports the Sheaf copy or uses `RingTheory.powerSeriesRingSubfields`.
The two Sheaf consumers named in the retirement inventory are already absent. The existing
upstream consumers already use the upstream module and renamed theorem, so require no edits.
No adopted source file, definition, target, or public import is changed.

Validation: an independent scratch theorem states the complete old signature and applies the
upstream theorem with precisely the original arguments. Both existing upstream consumers compiled
individually through lcompile.py (2.8 s and 3.3 s). The replacement signature check compiled without warnings (1.3 s).
`tools/downstream.py Sheaf.RingTheory.PowerSeriesRingSubfields --uses
powerSeriesRingSubfields` reports zero downstream modules and only the declaration itself
as a name occurrence. The delivery dry run checks remaining import references.

Change record: `coord/changes/retire-power-series-ring-subfields.md`.

## Proved and sorry left

This is a retirement repair, with zero original holes and zero remaining holes.
Holes closed: none (0 of 0). Holes added: none. Split off: none.
The already proved `RingTheory.powerSeriesRingSubfields` is withdrawn as an unused duplicate;
its full statement is retained as the already proved upstream theorem
`RingTheory.iInter_frobenius_subfields_mvPolynomial_mvPowerSeries`.

## No longer needed

Module pruned: `Sheaf.RingTheory.PowerSeriesRingSubfields`.
Its declaration `RingTheory.powerSeriesRingSubfields` is replaced in the DAG attachment by
`RingTheory.iInter_frobenius_subfields_mvPolynomial_mvPowerSeries`.
All imports of the withdrawn module disappear with that module. There are no current consumer
imports to remove. The upstream theorem retains the identical finite-basis and intersection
proof dependencies; none of those modules or nodes is pruned. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 proof brief describes a module with holes, but this item is a retirement
repair and already has zero holes. The retirement inventory's two Sheaf consumers no longer
exist. The DAG already names the renamed upstream declaration but still attaches it to the
Sheaf file and records the old theorem name in `lean.statement`. This delivery makes those
fields consistent with the existing upstream theorem.

Searches through msearch.py (LeanFinder, Loogle, grep) were completed. No Mathlib replacement
is needed because the upstream library already has the exact complete proof.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
