## What changed

Filled both proofs in `Sheaf.AlgebraicTopology.ProductIntervalNullhomotopy` without changing
any existing statement, definition, public import, or attribute. `coordinate_laws` proves the
coordinate maximum and unit-vector bounds directly. `nullhomotopy` follows the node's four
steps: inject the interval into the finite product of bounded coordinates, subtract the two
existing prism identities, kill constant images of positive-dimensional strict chains, and
supply the augmentation section in degrees zero and minus one. Below minus one the basis is
empty. Private, proved helpers carry out the generator calculations. Added proof-only imports
of `Mathlib.Tactic.Abel` and `Mathlib.Data.Fintype.Pi`.

Validation: the full proof compiled through `lcompile.py` in 4.9 seconds. The unused-binder
warning was addressed by using the preserved dimension bound `hr` to exclude the impossible
zero-dimensional case before the coordinate calculations; delivery checks validate that revision.

The original DAG proof, proof dependencies, and proof origin already describe this route and
need no change. No shared module or definition was edited.

## Proved and sorry left

Closed the two existing holes:

- `AlgebraicTopology.AugmentedPosetChains.ProductInterval.coordinate_laws`.
- `AlgebraicTopology.AugmentedPosetChains.ProductInterval.nullhomotopy`.

Both realize `lem-sfb-product-interval-nullhomotopy`. Zero holes remain in the item, and zero
holes were added or split off. The proof uses the existing `map_id` and `prism_identity`
declarations from `Sheaf.AlgebraicTopology.AugmentedPosetChainPrism`; their proofs and the
chain-complex construction's proof obligations remain with their existing dependency items.

## No longer needed

None. No public or proof import was removed, and all original DAG dependencies remain needed.
The current proof follows the planned route and prunes no module or node.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The proper interval uses the partial-order strict inequality,
so its coordinates may include zero; the proof uses coordinatewise bounds and a strict inequality
in the distinguished coordinate only. It therefore also covers zero bounds in other coordinates,
the one-coordinate interval, and the zero coefficient ring.

The search found no direct Mathlib contraction theorem for this construction. Loogle supplied
`List.pairwise_replicate`, used to kill constant strict chains in positive degrees. The existing
node already correctly describes the augmentation correction and the sign of the prism difference.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
