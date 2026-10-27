## What changed

Implemented the derived part of
`WeilConjectures.IntegralLineReduction.integral_line_normalized_evaluations` without
changing its statement or its public imports. The proof specializes
`ringedTensorComparison_extension` to each signed degree-zero line, constructs a
natural comparison on every complex, and proves its equality with the prescribed
`integralLineRepresentativeIso` on each good representative. The existing proved
localization helpers in `LineUnboundedDerivedTensor` then descend the two chain
cancellations and their triangle. Explicit cancellation of the two representative
comparisons proves both `DerivedEvaluationFormula` clauses.

Added `Sheaf.Paper.IntegralLineChainEvaluations`, containing the actual total-tensor
functor `chainTensor`, the generator predicate `ChainEvaluationFormula`, and the
remaining chain-only evaluation theorem. These definitions contain no postponed
proof or chosen witness. Updated the assigned node to describe the implemented
comparison and localization argument and attached a new node to the chain step.

The generic node `lem-sfb-ringed-tensor-comparison-extension` is used as a tool:
it extends a specified tensor comparison to an arbitrary first complex with a
K-flat second factor. This changes no unit argument and preserves the exact
recorded tensor model. Its source and Lean statement were read. The unit
`sk-prop-an` and its realized steps are unchanged.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralLineReduction.integral_line_normalized_evaluations`
(node `lem-pur-integral-line-normalized-evaluations`). Its proof is complete from
the imported declarations and has no internal sorry.

Added one hole:
`WeilConjectures.IntegralLineReduction.integral_line_chain_evaluations`
(node `lem-pur-integral-line-chain-evaluations`). This is a decomposition, with
one original hole closed and one strictly lower hole added, not a net hole
reduction. The new statement concerns chain isomorphisms on ordinary unbounded
complexes and their generator formulas and triangle; it does not assert any
localization, derived natural isomorphism, or recorded representative equation.
The implemented parent supplies all of those additional conclusions. The
remaining hole is exactly `:= by sorry`, with its source and full proof in its
docstring and node.

The private helpers `single_kflat` and `chain_comparison` are proved.
No existing library hole was added or changed outside the assigned module.

Validation: the new chain module compiled in 44.6 seconds. The final parent
compiled without warnings in 36.1 seconds through `lcompile.py`; both are below
the per-file limit. The sole remaining sorry is the named chain theorem above.

## No longer needed

No original import was removed. No module is withdrawn or claimed globally
unreachable. The original direct parent dependency
`lem-pc-sheaf-modules-tensor-closed` is no longer a direct dependency of the
implemented derived argument; its ordinary tensor constraints remain needed in
the new chain-only node. The old parent's unformalized chain calculation is now
precisely located there. `lem-weil-signed-line-tensor-equivalence`,
`lem-pur-line-unbounded-derived-tensor`, and
`def-pur-integral-line-reduction-data` are retained and used.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The original proof plan did
not name the comparison theorem needed to move from the published line tensor
presentation to the recorded ordinary model. The already proved
`ringedTensorComparison_extension` supplies that step with its exact simultaneous
K-flat normalization, so no new normalization or localization obligation is
introduced. The chain-only remainder is strictly below the twice-split original
obligation: the derived model, comparisons, and triangle descent have been
implemented rather than passed to another theorem.

Edge cases checked against the source and the formula: exponent zero uses
multiplication on the unit; a negative exponent exchanges the positive power and
its dual with only the `neg_neg` transport; empty covering members and zero
coefficient sections do not require a nonzero basis coefficient. The new theorem
is on all unbounded complexes and adds no completeness, constructibility,
residue-characteristic, or finite-reduction condition.

## New nodes

`lem-pur-integral-line-chain-evaluations` is the pre-localization part of original
proof steps 1 and 2. It records the two natural chain cancellations, their exact
total-generator formulas, and the chain triangle. Its proof uses the existing
ordinary sheaf line inverse-pair statement and degree-zero total-tensor collapse.
Searches of LeanSearch, Loogle/LeanFinder, project and Mathlib sources, and the
whole blueprint found no statement of this chain formula for the signed powers
in the recorded tensor presentation. No existing definition or statement changed,
so no change record or consumer adaptation is needed.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
