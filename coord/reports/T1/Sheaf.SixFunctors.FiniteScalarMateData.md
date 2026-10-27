## What changed

Filled the three theorem proofs in `Sheaf.SixFunctors.FiniteScalarMateData`.
`retainedIndex_succ` uses natural-number subtraction cancellation and positivity.
`retainedIndex_mono` uses monotonicity of multiplication and truncated subtraction.
`quotientSquare` reuses the existing proved
`PurCompactSupport.ramified_quotient_square`: split the ramification exponent into
zero (contradicting positivity) and successor, then explicitly change to the
existing square, whose exponents and transported maps are definitionally equal.
All signatures, definitions, docstrings and imports are unchanged.

Validation: `lcompile.py` compiled the final module without warnings in 18.9 seconds.

Searches: LeanFinder on natural-number subtraction and multiplication;
Loogle on `Nat.sub_add_cancel`; repository searches for retained-index lemmas and
ramified quotient squares. The existing coefficient-square theorem gives the
shortest route, with no new dependency or statement.

## Proved and sorry left

Closed all 3 original holes:

- `WeilConjectures.FiniteScalarMate.retainedIndex_succ`
- `WeilConjectures.FiniteScalarMate.retainedIndex_mono`
- `WeilConjectures.FiniteScalarMate.quotientSquare`

All belong to `def-coef-finite-scalar-mate-data`. No holes remain in the item;
no holes were added or split off. The monotonicity proof includes e = 0 and equal
indices; the successor formula correctly retains the positivity assumption.
The coefficient square reuses the theorem valid also for m = n, e = 1 and empty
schemes.

## No longer needed

None. No imports, nodes or modules were removed. The node has no proof steps or
proof dependencies to prune; the existing quotient-square proof is reused rather
than duplicated. All existing public imports are retained for the module's
canonical definitions and interface.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The module's quotient-square obligation was
already proved under the positive-exponent notation in its existing public
coefficient-comparison dependency. No DAG route or definition change was needed.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
