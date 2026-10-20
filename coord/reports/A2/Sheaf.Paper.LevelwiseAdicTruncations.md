## What changed

Restored `lean/Sheaf/Paper/LevelwiseAdicTruncations.lean` from its quarantined source.
The stale `LocallyClosedStratification` type in
`pbc_levelwise_truncations_constructible` is replaced by the current
`AlgebraicGeometry.Scheme.Stratification` declaration, which carries the same stratum
schemes and immersions. The prior compile-stability repair is retained: local priorities
for the standard derived-category instances, local irreducibility for the universal
scalar-extension definitions, and the private `scalar_unit_transport` lemma used by
`pbc_levelwise_truncation_transitions`. No target signature or source-library module is
changed.

## Proved and sorry left

The quarantined module compiles cleanly. This is a definition/compatibility repair and
closes no existing proof holes. The seven named theorem proofs intentionally remain
`sorry`, as in the quarantined source, with their existing DAG attachment:

- `pbc_adic_levelwise_truncations`
- `pbc_reduction_adic_tower_laws`
- `pbc_levelwise_tor_of_uniformizer_injective`
- `pbc_levelwise_truncations_constructible`
- `pbc_levelwise_truncation_counterexample`
- `pbc_levelwise_truncation_origins`
- `pbc_levelwise_truncation_compatible_origins`

No new `sorry` is added.

## No longer needed

None. The restored module retains the source imports because its declarations and their
proof APIs use them; no DAG node or module can be pruned by this repair.

## Where the brief, the DAG or earlier work was wrong

The quarantined source used the removed identifier `LocallyClosedStratification`, while
this adopted source tree provides the scheme-level `Stratification` used by
`IsUniformlyBoundedConstructibleAdicTower`. The mathematical hypothesis is unchanged.


The interface repair is recorded in `coord/changes/levelwise-adic-truncations-rework.md`.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
