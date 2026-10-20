## What changed

Added a real Lean composition proof for `point_sections_finite_reduction`. The target now
obtains the comparison, boundedness, and normalized flat-complex compatibility from three
named intermediate theorems. Those three intermediate theorems are documented and tracked
as new DAG nodes, with their proofs intentionally split off for follow-up workers.

## Proved and sorry left

The target theorem `point_sections_finite_reduction` is proved by composition. The following
strict subresults remain as named `sorry` declarations and each has a new DAG node:

- `point_sections_finite_reduction_iso`
- `point_sections_finite_reduction_bounded`
- `point_sections_finite_reduction_complex`

No definition contains `sorry`.

## No longer needed

None. The existing proof imports and approved tool dependencies remain needed by the
module's definitions and intermediate statements.

## Where the brief, the DAG or earlier work was wrong

The original eight-step proof plan was too large to place in one theorem body. It has been
split into three strict mathematical subresults; the final theorem is unchanged and
combines them directly.

## New nodes

Created `lem-trf-point-sections-finite-reduction-iso`,
`lem-trf-point-sections-finite-reduction-bounded`, and
`lem-trf-point-sections-finite-reduction-complex` in the trace-formula chapter. Their
statements are the exact Lean signatures of the corresponding named intermediate theorems.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
