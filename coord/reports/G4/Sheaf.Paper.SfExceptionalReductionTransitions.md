## What changed

Filled `WeilConjectures.SfExceptionalReduction.quotient_laws` in
`Sheaf.Paper.SfExceptionalReductionTransitions`. Composition of the sheafified
quotient factors follows from `Ideal.Quotient.factor_comp_apply`; equal indices
follow from `Ideal.Quotient.factor_eq` and the constant-sheaf functor's identity
law. Projection compatibility follows by natural-number induction from the
adjacent `limit.w` equation of `integralCoefficientSheafSystem`. This follows
the quotient calculation already recorded in the declaration's docstring and
the node's last proof step, with no change of route or interface.

Remote single-file compilation succeeded (43.3 seconds). Both equal indices and
arbitrary gaps between levels are included in the proved statement. No imports,
definitions, signatures, or DAG records changed.

## Proved and sorry left

Closed one of the three original holes:

- `WeilConjectures.SfExceptionalReduction.quotient_laws`.

Two original holes remain unchanged, both attached to
`lem-sf-exceptional-reduction-transition-comparison`:

- `WeilConjectures.SfExceptionalReduction.restrictionMate_isIso`.
- `WeilConjectures.SfExceptionalReduction.exceptionalReductionTransitionComparison`.

Added holes: none. Split-off statements: none. This is a partial proof delivery,
not a decomposition of either remaining theorem.

## No longer needed

None. No import, module, or node is pruned: the remaining two declarations still
require the recorded adjunction, scalar-comparison, and supported-triangle plan.
The quotient proof itself only uses the existing imports.

## Where the brief, the DAG or earlier work was wrong

No discrepancy was established. The main theorem and restriction-mate theorem
still need their existing planned proofs; their statements and proofs in words
are preserved. No statement or definition repair is included.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
