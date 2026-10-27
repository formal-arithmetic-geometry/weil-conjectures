## What changed

Proved `WeilConjectures.integralQuotientRoos_homotopy` with its original statement.
The private constructions assemble ordinary quotient reduction and scalar restriction into an
additive module-valued tower, identify its degreewise complex tower with the specified native
tower, and compare the two presentations of the Roos fibre. The proof descends the localized
Roos functor and its augmentation through the homotopy quotient. The existing signed cone
calculus supplies exactness and shift compatibility. The pure-tensor characterization of the
quotient units and naturality of the zero-second-coordinate cocone lift give the required
normalization to `roosUnit`.

Added proof-only imports of `StrictRoosHomotopyFunctor` and `RoosConeCalculus`, and private
access to the already proved construction helpers of `IntegralDerivedOperationsOnSlices`.
Updated the item's node proof and proof origin to describe this argument. No existing
statement, public import, shared definition, or other existing module was changed.

## Proved and sorry left

Closed the sole original hole: `WeilConjectures.integralQuotientRoos_homotopy`
(node `lem-sf-integral-quotient-roos-homotopy`). Holes closed: 1. Holes added: 0.
No `sorry` remains in the delivered module. No obligations were split off; every private
helper is proved.

Validation: the complete item compiled through `lcompile.py` in 43.4 seconds, without warnings.

## No longer needed

None. All three declared proof dependencies remain used:
`def-pur-integral-derived-operations`, `lem-pur-strict-roos-homotopy-functor`, and
`lem-pe-roos-cone-calculus`. No existing import was removed and no node or module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The module-valued quotient tower is made explicit so
that Mathlib's generic complex and homotopy-quotient APIs apply before comparison with the native
complex-valued tower. The blueprint unit route and the original conclusion are preserved.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
