## What changed

Proved `Module.isClosed_support_and_isCompact_compl` from Mathlib's closedness theorem and
`PrimeSpectrum.isCompact_isOpen_iff_ideal`. Added the intermediate module
`Sheaf.RingTheory.FinitelyPresentedSupportIdeal`, whose single named theorem isolates the
maximal-minor support calculation and remains `sorry`.

## Proved and sorry left

Closed the sorry in `Module.isClosed_support_and_isCompact_compl`.
The added theorem `Module.exists_fg_ideal_eq_support` remains as one intentional sorry;
its node is `lem-pur-finitely-presented-support-ideal`.

## No longer needed

The parent proof no longer directly imports or uses the localization-homeomorphism,
spectrum-compactness, adjugate, or Cauchy--Binet modules; those details are encapsulated by
the intermediate theorem. The parent node's proof dependencies were pruned to the new node.

## Where the brief, the DAG or earlier work was wrong

The original six-step proof plan is mathematically sound but too large to complete within
this worker session. No statement or definition was changed.

## New nodes

`lem-pur-finitely-presented-support-ideal` records the strictly smaller maximal-minor
support calculation, sourced to Stacks Tag 051B. It is stated in
`lean/Sheaf/RingTheory/FinitelyPresentedSupportIdeal.lean`. The import change is recorded in
`coord/changes/FinitelyPresentedSupportComplement-imports.md`.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
