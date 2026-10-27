## What changed

Proved five four-stage structural coherence theorems in
`Sheaf.Paper.ProjectionFormulaCoherence` directly from the corresponding fields of
`compactSupportProjectionFormula`: naturality, compactification, composition, pentagon,
and proper identification. The field-stage laws use the existing True domains.
Proved the realization equation by cancelling the specified target comparison against
its inverse. All existing statements, definitions, docstrings, and public imports are
unchanged.

## Proved and sorry left

Closed 6 of the 15 original holes:

- `WeilConjectures.sixFunctorProjection_naturality`
- `WeilConjectures.sixFunctorProjection_compactification`
- `WeilConjectures.sixFunctorProjection_composition`
- `WeilConjectures.sixFunctorProjection_pentagon`
- `WeilConjectures.sixFunctorProjection_proper`
- `WeilConjectures.sixFunctorProjection_realization`

Added zero holes and split off zero statements. The five structural proofs depend on
`WeilConjectures.compactSupportProjectionFormula`, an existing named theorem whose proof
still contains sorry; this is use of the declared dependency, not an axiom-free completion
of the targets. The realization proof uses only the actual defining conjugation and
category/isomorphism laws.

The following 9 original holes remain, all attached to `prop-sf-pf-coherence`:

- `WeilConjectures.sixFunctorProjection_baseChange_integral`
- `WeilConjectures.sixFunctorProjection_baseChange_rational`
- `WeilConjectures.sixFunctorProjection_baseChange_common`
- `WeilConjectures.sixFunctorProjection_identity`
- `WeilConjectures.sixFunctorProjection_baseChange_finite`
- `WeilConjectures.sixFunctorProjection_reduction_finite`
- `WeilConjectures.sixFunctorProjection_reduction_integral`
- `WeilConjectures.sixFunctorProjection_reduction_rational`
- `WeilConjectures.sixFunctorProjection_reduction_common`

## No longer needed

None. The remaining original holes still need the node's open/proper pasting,
normalization, and coefficient-transport route. No module or node is withdrawn, and
no remaining planned dependency is declared unnecessary.

## Where the brief, the DAG or earlier work was wrong

`ProjectionFiniteReduction` states a change of positive finite coefficient level on
finite-Tor inputs. It does not directly prove this item's updated all-ideal square,
which tensors with a possibly nonperfect quotient in the original coefficient category.
The latter square is an action-associativity equation. A fully proved generic
pro-etale action equation exists privately in `FiniteProjectionActionLaws`; specializing it exposed expensive conversion of monoidal instance terms. A generic
rearrangement of that equation compiles, but specialization to this item has not yet
compiled. These scratch experiments are not delivered as proofs.

For base change, `OpenBaseChangeSquare` and `CompactificationProjectionPasting` supply
canonical factor equations and a conditional categorical pasting result. Identifying
those maps with the supplied operation coordinates remains actual proof work; this
packet does not claim that the conditional theorem alone closes the displayed square.

Validation: the item module compiles successfully through `lcompile.py` (55.6 seconds),
with 9 original theorem holes left and no new holes.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
