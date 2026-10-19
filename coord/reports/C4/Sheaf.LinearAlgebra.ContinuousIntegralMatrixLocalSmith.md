## What changed

Proved `Padic.continuous_integral_matrix_local_smith` with its signature unchanged.
Retained and completed the earlier sandbox work. Added two fully proved auxiliary
modules: `Sheaf.LinearAlgebra.DvrMatrixSmithPowers` and
`Sheaf.LinearAlgebra.ContinuousIntegralDiagonalRankLocus`.

The scalar lemma constructs source and target bases from Mathlib Smith form of the
image, a kernel basis, and lifted image basis vectors. It absorbs scalar units and
sorts the uniformizer powers. The diagonal lemma divides the error in the pivot
columns to construct a continuous matrix equal to the identity at the centre.
On its open invertibility locus its inverse fixes the pivot columns; an explicit
square-zero column correction clears the remaining pivot rows. A nonzero residual
entry would give a nonzero minor of size r+1, contradicting the rank bound.

The item uses cokernel equivalence only to obtain equality of matrix ranks. It
applies the scalar lemma at the centre and the diagonal lemma to the conjugated
family, then transports the neighbourhood and composes factors. No existing
statement or definition was changed; no consumer adaptations are needed.

All three modules compiled together on the project server (diagonal: 4.7 s,
scalar: 3.4 s, item: 4.7 s). After removing two style warnings, the final diagonal
module also compiled alone without warnings in 4.2 s. The delivery dry run checks
the compiled declarations and axioms again.

## Proved and sorry left

Closed the item's sole original hole:
`Padic.continuous_integral_matrix_local_smith` (1 of 1).
The new auxiliary declarations `Matrix.exists_smith_pow` (node
`lem-sfb-dvr-matrix-smith-powers`) and
`Padic.continuous_integral_diagonal_rank_locus` (node
`lem-sfb-continuous-integral-diagonal-rank-locus`) are both proved.
Holes added: zero. Holes left in all three delivery modules: zero.
The earlier unproved diagonal split has been completed in this resumed session.
Existing coefficient-extension theorems are used through their current interface;
this delivery does not claim to close their upstream obligations.

## No longer needed

Removed the proof imports `Sheaf.LinearAlgebra.ContinuousIntegralPivotSplitting`
and `Sheaf.RingTheory.DvrCyclicSummandCancellation`. Neither module nor its node
(`lem-sfb-continuous-integral-pivot-splitting`,
`lem-sfb-dvr-cyclic-summand-cancellation`) is needed by this proof, directly or
through its two auxiliaries. In particular, no residual-cokernel cancellation,
pivot induction, or classification of positive elementary divisors in the cokernel
is required. Their other consumers are unaffected.

The direct `Mathlib.LinearAlgebra.FreeModule.PID` import moves from the item to
the scalar auxiliary, where it is used. Its scalar Smith Mathlib leaf
`lem-sc-dvr-saturation-line-smith-normal-form` remains needed. The coefficient
extension node `def-weil-l-adic-coefficient-extension` remains needed.
Both new auxiliary nodes are needed and fully proved. No module is withdrawn.
The unit's statement and proof steps are preserved: these changes are below them.

## Where the brief, the DAG or earlier work was wrong

The inherited node search records lacked LeanSearch. The first full preflight
returned both new nodes for that metadata omission; dedicated LeanSearch queries
were run and their results recorded. No matching theorem was found.

The inherited report described a remaining diagonal hole and an induction proof.
The current proof instead uses a direct near-identity matrix and a rank/minor
argument, and closes that hole. The DAG and auxiliary docstring now describe this
actual route. The generic adic argument avoids expensive unfolding of
`Ideal.openAddSubgroup` by using `isAdic_iff` to obtain openness of ideal powers.
Explicit unit-value coercions avoid confusing matrix inversion with unit inversion.

HRS Theorem 6.12(2) provides the continuous integral division context; the local
Smith and fixed-diagonal statements here are agent arguments, not verbatim HRS
theorems. Stacks Tag 00PD characterizes DVRs; the scalar Smith theorem used here
is Mathlib's finite-free Smith API, as the new scalar docstring records.

The formulas include empty dimensions, r=0, zero matrices and exponent-zero pivots.
For r=0 the square-zero correction is zero and the rank/minor argument forces
F=0; for a full-width or full-height diagonal the residual block is empty.
The algebraic quotients used for divisions are unique by cancellation in a domain;
no arbitrary witness is chosen from an unproved existence statement.

## New nodes

`lem-sfb-dvr-matrix-smith-powers` records the proved rectangular scalar Smith
presentation, with sorted uniformizer powers and pivot count equal to rank.
`lem-sfb-continuous-integral-diagonal-rank-locus` records the proved local
reduction near a fixed diagonal under a rank bound. Its proof has no pivot or
cyclic-cancellation dependency. Both nodes retain the item's chapter and unit.
No change record is required because existing statements and definitions are unchanged.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
