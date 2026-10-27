## What changed

Added `Sheaf.Paper.NormalizedVectorPurityScalarCore`, which states the strictly smaller
source-map invertibility and normalized mate equation needed by the fixed-witness theorem.
The item module imports this core statement and proves the remaining compact-support
invertibility and mate invertibility clauses by scalar coherence and categorical cancellation.
The core theorem is intentionally left as the one named split-off proof obligation.

## Proved and sorry left

The item theorem `scalarReduction_compatibility_of_witnesses` is proved.  Its compact-support
map and mate-map clauses are closed using `etaleCompactScalarCoherence` and
`IsIso.of_isIso_comp_left`.

One sorry remains in the new declaration
`scalar_source_compatibility_core` in
`Sheaf.Paper.NormalizedVectorPurityScalarCore`; it is the source-map invertibility and
normalized purity-family compatibility substatement, with node
`lem-pur-normalized-vector-purity-scalar-source-core`.

## No longer needed

No proof-dependency imports or DAG nodes were pruned.  The attempted direct use of the generic
integration transpose theorem was not retained because the prescribed normalized source map
requires the split-off source compatibility statement.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan omits the explicit identification between the ordered scalar tensor/pullback
comparison used by the generic mate theorem and `purityScalarSourceMap`; this is a genuine
strictly lower source-compatibility step and is recorded as the new node above.

## New nodes

`lem-pur-normalized-vector-purity-scalar-source-core` records the source-map invertibility and
mate compatibility substatement.  Its Lean declaration is in
`lean/Sheaf/Paper/NormalizedVectorPurityScalarCore.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NormalizedVectorPurityScalarCompatibility": "f76fcde2eecc7181e55b0b0dfc9478505cddb61b", "Sheaf.Paper.NormalizedVectorPurityScalarCore": "79ab540bff9c6222e34034e9aca77a828c796023"}, "results": {"Sheaf.Paper.NormalizedVectorPurityScalarReduction": {"hash": "ea432286482215d7da9186bbbc260a863a2c65a0", "status": "OK"}}, "seconds": 31, "time": "2026-10-28T03:45:31+0800", "transitive": 0, "version": 1}
```

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
