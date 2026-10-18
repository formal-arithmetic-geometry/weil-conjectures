## What changed

Added explicit proved helper calculations for the decalage interval successor and spectral
interval embedding, and decomposed the top coherence theorem into differential and successor
compatibility declarations. The top theorem is proved by constructing the two fields from these
strictly smaller statements.

## Proved and sorry left

Closed the original `filteredComplex_decalage_page_coherence` sorry. Two strictly smaller
statements remain sorry: `filteredComplex_decalage_page_differential_coherence` and
`filteredComplex_decalage_page_successor_coherence`; their nodes and source-level proof plans
are recorded below.

## No longer needed

No stated proof dependency was removed. The helper proof uses the Mathlib spectral-sequence
homology-data API, `filteredComplexDecalageIntervalIso_map`, and the existing representative
transition theorem.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan leaves the differential and successor chases as one monolithic theorem.
The Lean API supports a clean decomposition into the two independent compatibility equations;
the top statement is unchanged.

## New nodes

`lem-sp-filtered-complex-decalage-page-differential-coherence` and
`lem-sp-filtered-complex-decalage-page-successor-coherence` are the two strictly smaller
components left for parallel proof.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
