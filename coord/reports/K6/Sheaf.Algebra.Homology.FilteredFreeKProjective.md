## What changed

Rewrote the finite-stage successor proof to pass the componentwise split and quotient
hypotheses directly to `isKProjective_of_filtered_free_step`. Rewrote the final theorem to
pass the finite-stage theorem directly into the updated upstream
`filtered_free_telescope_assembly`. The theorem signatures and imports are unchanged.

## Proved and sorry left

All three declarations in `Sheaf.Algebra.Homology.FilteredFreeKProjective` remain proved:
`CochainComplex.isKProjective_of_filtered_free_stage`,
`CochainComplex.isKProjective_of_filtered_free_telescope`, and
`CochainComplex.isKProjective_of_filtered_free`. No `sorry` remains in the module, so the
closed-hole count is 0 and the split-off count is 0.

## No longer needed

No imports or DAG nodes became unnecessary. The proof still uses the finite-stage theorem,
`WeilConjectures.Algebra.Homology.FilteredFreeKProjectiveStep`, and the upstream telescope
assembly theorem.

## Where the brief, the DAG or earlier work was wrong

The shared module already had complete proofs and no `sorry`, despite being dispatched as an
item. The only actionable repair was to make the proofs explicitly apply the current upstream
assembly and split-extension interfaces; no statement or definition required correction.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
