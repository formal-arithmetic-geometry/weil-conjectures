## What changed

Proved all three theorems in `Sheaf.Paper.KunBaseChange` without changing any
existing signature, definition, or visibility. Successive base change is the
component of the recorded horizontal-pasting law. The cube applies the upstream
horizontal-pasting law twice to the same outer commutative square and cancels
inverse-image composition comparisons. Two proved private helpers evaluate
pasting with specified composite arrows and perform categorical cancellation.
The identification follows by cancelling the right vertical isomorphism.

Added the proof-only import
`WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal` for its law on
arbitrary commutative squares. This is the same horizontal-pasting law already
used by the recorded dependency `Sheaf.Paper.ExchangeIdentityPasting`.
Single-file compilation passed with no warnings, in 10.1 seconds.

## Proved and sorry left

Closed three original holes:

- `AlgebraicGeometry.Etale.kun_bc_base_change`.
- `AlgebraicGeometry.Etale.kun_bc_base_change_cube`.
- `AlgebraicGeometry.Etale.kun_bc_base_change_identification`.

All belong to node `lem-kun-bc-base-change`. Zero holes remain in the item;
zero holes were added or split off. Both private helpers are fully proved.

## No longer needed

No imports removed and no planned dependency modules or nodes pruned. The cube
uses the stronger existing horizontal-pasting API for commutative squares;
separate proofs that its auxiliary squares are Cartesian are unnecessary for
this equation. The fibre-product projection equations suffice, including for
empty fibre products. The unit statement and route are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The cube's stated proof plan asks for
Cartesian identifications of the comparison squares, whereas the existing
upstream pasting theorem applies to all commutative squares, so those additional
identifications do not enter the Lean proof. A declaration-local heartbeat
allowance covers elaboration of the concrete derived-functor comparisons; the
single-file wall-clock limit is unchanged.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
