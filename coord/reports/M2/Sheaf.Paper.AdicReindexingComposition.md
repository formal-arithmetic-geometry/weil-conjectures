## What changed

Added `normalized_reindexing_composition_cancelled` in
`Sheaf.Paper.AdicReindexingCompositionCancelled`.  It isolates the representative
and scalar composition calculation after postcomposition by the inverse of the final
derived-pullback comparison.  The assigned theorem now applies that calculation and
restores the final comparison by an explicit inverse-composition cancellation.

The parent node `lem-sf-adic-reindexing-functoriality-comp` now records the cancelled
calculation as its sole proof dependency.  The new node
`lem-sf-adic-reindexing-functoriality-comp-cancelled` records the three original
composition dependencies and the proof step they support.

## Proved and sorry left

The assigned theorem
`WeilConjectures.AdicQbarRealization.normalized_reindexing_composition` is proved.
The new helper theorem
`WeilConjectures.AdicQbarRealization.normalized_reindexing_composition_cancelled`
retains one `sorry` for the representative, entire-cone, scalar-coherence, and
finite-realization calculation.  Thus one of the original one sorries is closed and
one strictly smaller intermediate statement is split off.

## No longer needed

None.  The original three proof dependencies remain needed by the split-off
calculation, and the parent theorem imports the helper module.

## Where the brief, the DAG or earlier work was wrong

The original module's proof plan stated the full composition calculation but did not
separate the final invertible derived-pullback factor from the representative
calculation.  The delivery makes that cancellation explicit; no target statement or
definition was changed.

## New nodes

- `lem-sf-adic-reindexing-functoriality-comp-cancelled`: the composition equation
  after cancelling the final derived-pullback comparison.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicReindexingComposition": "f31e857ae4f4436ec86e59175ac78bfdf2e06648", "Sheaf.Paper.AdicReindexingCompositionCancelled": "50c7b158e873807ccaa7ef073bad8bc797266ef1"}, "results": {"Sheaf.Paper.AdicReindexingFunctoriality": {"hash": "bf857425a90d47854bbe0ca74d81cdad54f17e62", "status": "OK"}}, "seconds": 19, "time": "2026-10-28T07:07:15+0800", "transitive": 0, "version": 1}
```

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
