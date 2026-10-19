## What changed

Filled five proofs in `lean/Sheaf/Paper/LevelwiseAdicTruncations.lean` without changing
any existing statement, definition, visibility, or import. The DAG copy records the
direct canonical truncation API and adjunct argument used for these closed clauses.
Two proved private lemmas identify the exact-functor truncation comparison with the canonical counit and unit.
The levelwise cohomology theorem uses the existing derived-category truncation API
and proves both semilinear transition squares. Exact evaluation transports the same
cohomology formulas to the strict tower. Naturality follows by comparing two actual
triangle morphisms with identical middle components, using Mathlib's t-structure
triangle-map uniqueness. The finite-extension theorem applies the general adic theorem.
Transition compatibility uses the first two squares of the supplied normalized triangle comparison, naturality
of the scalar-adjunction unit, and the universal properties of the canonical truncations.

## Proved and sorry left

Closed five of the original twelve holes:

- `AlgebraicGeometry.Scheme.pbc_levelwise_truncation_cohomology`.
- `AlgebraicGeometry.Scheme.pbc_strict_tower_truncation_cohomology`.
- `AlgebraicGeometry.Scheme.pbc_levelwise_truncation_naturality`.
- `AlgebraicGeometry.Scheme.pbc_levelwise_truncation_transitions`.
- `AlgebraicGeometry.Scheme.pbc_levelwise_truncations` (from the existing general theorem).

Seven original holes remain, all attached to `prop-weil-pbc-levelwise-truncations`:

- `AlgebraicGeometry.Scheme.pbc_adic_levelwise_truncations`.
- `AlgebraicGeometry.Scheme.pbc_reduction_adic_tower_laws`.
- `AlgebraicGeometry.Scheme.pbc_levelwise_tor_of_uniformizer_injective`.
- `AlgebraicGeometry.Scheme.pbc_levelwise_truncations_constructible`.
- `AlgebraicGeometry.Scheme.pbc_levelwise_truncation_counterexample`.
- `AlgebraicGeometry.Scheme.pbc_levelwise_truncation_origins`.
- `AlgebraicGeometry.Scheme.pbc_levelwise_truncation_compatible_origins`.

No holes added or split off. The five closed proofs are a partial delivery; the
normalization construction, Tor calculations, constructibility and origin coherence
remain as their existing named obligations. The strict-tower and levelwise cohomology
proofs and the naturality proof use no new unproved intermediates.

## No longer needed

None. No import was added or removed. The original dependency modules remain relevant
to the seven untouched obligations and to the public statements and definitions.
Mathlib's existing canonical truncation and triangle-map uniqueness APIs implement the
formal parts of steps 1 and 3 directly; no separate tower-abelian or triangle-extension
proof is needed for those closed clauses. Those nodes remain needed for the other
clauses of the original plan, so no node or module is claimed as globally pruned.
The unit `sk-rem-rest` has no realized statement or proof steps, and its route is kept.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The retained four proofs compiled
cleanly against the current published build in 10.4 seconds. The complete five-proof
version then compiled cleanly without warnings in 9.3 seconds through `lcompile.py`.
Some compile calls
received no server answer and were retried. Provider interruptions did not reset the
sandbox or the original deadline.
The exact scalar-restriction and evaluation APIs require explicit functor unfolding
and cohomological-bound instances at their canonical truncation objects. The proof
uses declaration-local elaboration settings without altering the public interface.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
