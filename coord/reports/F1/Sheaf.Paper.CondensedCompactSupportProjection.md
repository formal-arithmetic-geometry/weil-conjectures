## What changed

Proved `condensedProjection_id` in `lean/Sheaf/Paper/CondensedCompactSupportProjection.lean`.
The proof adds private categorical normalization lemmas for derived identity coefficient squares,
then applies the proper and open scalar pasting calculation. Proof-only imports (including private generic derived-square helpers from
`Sheaf.Paper.ProperIntegralRationalScalarComparison`) provide the
existing derived composition, coefficient-square action, and adjunction identity APIs.

## Proved and sorry left

Closed the original sorry in `condensedProjection_id`.
The remaining original sorries are `condensedProjection_comp`, `fieldProperOpen_existsUnique`,
`condensedProjection_refinement`, and `fieldRefinement_comp`. All five original holes and the four retained holes belong to
`def-pur-condensed-compact-support-projection`. Closed 1 of 5 holes; added 0; split off 0.
No definitions or existing public signatures were changed.

## No longer needed

No planned declarations, nodes, or modules were removed. The identity proof uses the derived
identity-square and scalar normalization route; all remaining declarations are still needed by the
unfinished parent proofs and the unit route.

## Where the brief, the DAG or earlier work was wrong

The DAG proof text did not spell out the derived identity-square normalization required for the
identity target. The proof supplies that normalization privately from the existing derived
adjunction and coefficient-square declarations, while preserving the public statement and route.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
