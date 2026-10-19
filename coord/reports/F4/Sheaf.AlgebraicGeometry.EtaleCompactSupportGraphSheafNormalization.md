## What changed

Added a proved reduction of the target to the named transpose theorem. The transpose theorem
is stated as a strict intermediate result and remains the sole split-off hole; the target theorem
now combines it with injectivity of the adjunction hom equivalence.

## Proved and sorry left

`compactSupportGraphSheafComparison_normalization` is proved from
`compactSupportGraphSheafComparison_normalization_transpose`. The split-off transpose theorem
retains one `sorry`, with its DAG node in the delivery.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The DAG plan correctly identifies the graph and complement restriction calculation. The
compactification projection coherence is not exposed by an existing library lemma and was not
completed in this delivery.

## New nodes

`lem-asd-compact-support-graph-sheaf-normalization-transpose` records the split-off transpose theorem and its remaining proof obligation.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
