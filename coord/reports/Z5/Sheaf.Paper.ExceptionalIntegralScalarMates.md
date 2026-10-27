## What changed

Added the named intermediate theorem `exceptionalIntegralScalarMates_core`, isolating the
Mates, finite-level ReductionMates, and SystemMates clauses from the final arithmetic
ramified-index witness clause. Added the corresponding DAG node. The original theorem
signatures and all existing definitions are unchanged.

## Proved and sorry left

No existing theorem hole was fully closed. The new theorem
`exceptionalIntegralScalarMates_core` is a named split-off `sorry` for the strictly
smaller non-index system-mate conclusion. The original
`exceptionalIntegralScalarMates` and `ramifiedRecovery` holes remain unchanged. No
`sorry` occurs in a definition.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The parent proof plan combines the system mate construction with an independent
arithmetic witness construction. The system part can be isolated as a strictly smaller
statement, but the dependent transport from the selected stage `e*(n+1)` to the
zero-based index `m = e*(n+1)-1` requires a dedicated transport lemma; it was not
silently replaced by an invalid definitional equality.

## New nodes

`lem-sf-exceptional-integral-scalar-mates-core` records the split-off core conclusion
and its remaining proof obligation.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
