## What changed

Added the explicit identity cancellation sublemma module and used it to reduce
`properOpenComparison_id` to the unit-counit cancellation statement. The composition
proof remains open.

## Proved and sorry left

Closed no original hole. Added `properOpenComparison_id_aux` as a named intermediate
statement; its proof is left as `sorry`. Original sorries remain in
`properOpenComparison_comp`; the identity theorem is reduced to the intermediate theorem.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The planned six-step proof requires substantial derived mate calculations that were not
available as a single reusable declaration in the current library. The restriction helper
experiment was withdrawn before delivery.

## New nodes

`lem-weil-pbc-proper-open-comparison-identity-aux`: unit-counit cancellation for the
explicit identity proper-open identification, used by `properOpenComparison_id`.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
