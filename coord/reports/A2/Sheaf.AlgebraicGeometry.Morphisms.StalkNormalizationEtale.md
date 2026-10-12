## What changed
Added the affine-chart intermediate theorem `GaloisCover.stalk_normalization_etale_local_charts` and proved the target theorem by constructing its `Etale` structure from that chartwise statement. The geometric chart computation remains as one named `sorry`.

## Proved and sorry left
The target theorem `GaloisCover.stalk_normalization_etale` is proved from the local-chart theorem. The declaration `GaloisCover.stalk_normalization_etale_local_charts` remains a sorry; its node is `lem-sbc-stalk-normalization-etale-local-charts`.

## No longer needed
None; all original imports remain available for the geometric local-chart argument.

## Where the brief, the DAG or earlier work was wrong
The DAG treated the full etaleness claim as one indivisible statement. The Lean proof naturally factors through the defining affine-chart field of `Etale`.

## New nodes
`lem-sbc-stalk-normalization-etale-local-charts` records the remaining affine-chart geometric argument.

## Second reading by A2

1. The existing target declaration has the same signature as the repository version; only its proof body was changed, and the added local-chart theorem is a strictly narrower chartwise conclusion. Verdict: unchanged target statement.
2. The local-chart theorem is a true intermediate formulation of the affine-chart field of `Etale`; it is exactly what the target constructor requires. Its proof remains a named, documented `sorry` with a matching DAG node. Verdict: split is necessary and appropriately stronger only at the chart level.
3. The module compiles cleanly with the launcher; no forbidden declarations or sorry inside definitions were introduced. The target proof uses the local-chart theorem and preserves the required `Etale` construction.
4. The original imports are retained because the split theorem has the full geometric context and no import was shown redundant. Verdict: no pruning available.
5. The DAG nodes, Lean declarations, proof dependency for the target, and unit route agree: the target node uses `lem-sbc-stalk-normalization-etale-local-charts`, while that node records the remaining geometric argument. Verdict: consistent.

Changed only the target proof and added the documented local-chart theorem/node; no existing signatures or definitions were altered.
