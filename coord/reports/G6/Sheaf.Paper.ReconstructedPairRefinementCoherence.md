## What changed

Proved `WeilConjectures.ReconstructedPairRefinement.output_origin` in
`Sheaf.Paper.ReconstructedPairRefinementCoherence`, with all existing signatures,
definitions, attributes, imports and docstrings preserved.

Three proved private helpers compare derived functors through localization, transfer
lower bounds along the exact derived evaluation, and transfer the intrinsic origin
property between two site packages. The output proof applies the supplied normalized
Brown transport bound and its inverse-evaluation comparison. No equality of arbitrary
derived-system maps is inferred from finite evaluations.

The module compiled through lcompile.py without warnings in 35.8 seconds.
The unfinished multi-module sandbox draft was removed before delivery; none of its
new declarations or holes is included in this packet.

## Proved and sorry left

Closed one of the three original holes:
`WeilConjectures.ReconstructedPairRefinement.output_origin`
(node `lem-pur-reconstructed-pair-refinement-coherence`).

The two unchanged holes are:
- `WeilConjectures.ReconstructedPairRefinement.systemDown_isIso`
  (node `lem-pur-reconstructed-pair-refinement-coherence`).
- `WeilConjectures.ReconstructedPairRefinement.reconstructedPairRefinementCoherence`
  (node `lem-pur-reconstructed-pair-refinement-coherence`).

Holes added: zero. Split-off statements: zero. This is a partial proof delivery,
not a proof of the complete coherence assertion.

## No longer needed

None. No existing imports, declarations, modules or DAG dependencies are removed.
The unchanged coherence theorem still has its recorded proof route.

## Where the brief, the DAG or earlier work was wrong

The preliminary sandbox draft omitted `D₂.transport.finite` when applying the
normalized transport bound. The proof now installs that existing finite-ring witness.
There is no statement correction or departure from the unit route.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
