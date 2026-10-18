## What changed

Proved `integral_square_zero_matrix_lift` in
`Sheaf.SixFunctors.IntegralSquareZeroMatrixLift`, following all four steps of
`lem-sfb-integral-square-zero-matrix-lift`. The lifted inverse is already an input.
The proof maps both matrix errors to zero in the quotient, uses `RingCon.eq`
to show each entry belongs to the ideal, and proves their squares vanish by
`Finset.sum_eq_zero`. Distributivity, associativity, and additive cancellation
then establish the two inverse identities and equality of the corrections.

The theorem signature, documentation, and imports are unchanged. No definitions,
new declarations, or other modules were changed. The original DAG proof and
proof dependencies describe the implemented route, so no node update is needed.

Validation: `lcompile.py` compiled the completed file successfully in 2.5 seconds,
without warnings. The proof works for arbitrary rings and finite rank, including
rank zero; it makes no nontriviality or commutativity assumption.

## Proved and sorry left

Closed the one original hole: `integral_square_zero_matrix_lift`
(node `lem-sfb-integral-square-zero-matrix-lift`).

Proved 1 of 1 original sorries. Added 0 holes. There are no remaining sorries
in the delivered module and no split-off modules.

## No longer needed

None. No proof imports were added or removed. The sole declared dependency,
`def-weil-matrix`, is the Mathlib matrix definition used throughout the proof.
All four elementary steps of the original plan remain used; no project nodes
or modules are bypassed or pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect was found. The theorem already supplies
`C` and its lifting property, so the representative choice discussed in the
first DAG step requires no additional construction in this proof.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
