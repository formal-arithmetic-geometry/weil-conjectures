## What changed
Added a canonical-lift intermediate theorem and reduced the supplied-lift theorem to it using monicity of `iCycles`.

## Proved and sorry left
`cochainHypercohomologyLeftEdge_cocycle` is proved from the canonical-lift statement and the lift uniqueness argument. The canonical representative calculation remains sorry in `cochainHypercohomologyLeftEdge_canonical`.

## No longer needed
Removed imports of `CartanEilenbergExists`, `CartanEilenbergLeftExactCohomology`, and `TruncationHypercohomology`; the proof only uses the left-edge API and the canonical-lift theorem.

## Where the brief, the DAG or earlier work was wrong
The DAG plan omits the necessary canonical representative calculation as a separate intermediate theorem; it is split out here.

## New nodes
`lem-pc-hypercohomology-edge-cocycle-canonical`: canonical cycle-lift representative equation.

## Earlier second reading (a previous round; superseded)
Pending second reading.

## Second reading by Q2

1. Compared the delivered item module with the repository version. The theorem signature of `cochainHypercohomologyLeftEdge_cocycle` is unchanged; only its proof and proof-only imports changed. The added canonical theorem has a separate statement and node.

2. Compiled both delivered modules with `lcompile.py --all`; they compile without errors. The item theorem is proved. The canonical representative calculation remains the single named `sorry`, with its source, docstring, and DAG node. No definitions contain `sorry`, and no forbidden declarations were added.

3. Checked the canonical-lift statement against the supplied-lift theorem. It is the strictly simpler fixed-lift calculation needed by the uniqueness reduction, and is not duplicated elsewhere in the library. Its node records the source, proof plan, and declaration.

4. Verified pruning: the proof uses only `HypercohomologyLeftEdge` and the canonical-lift module. The former Cartan--Eilenberg and truncation imports are no longer needed by this proof and were removed. The unit route remains through the hypercohomology left-edge construction and the cocycle comparison node.

5. Checked that the DAG node and Lean declarations agree, including the canonical node and its `sorry` status. No target statement or existing declaration signature was changed.

Changed in this second reading: added this review section only; no Lean proof or statement changes were necessary.
