## What changed

Filled `AlgebraicGeometry.ProjectiveSpace.exists_standardUnitCocycle_normalization_offDiagonal` with a complete proof that obtains a pairwise Laurent expansion and then applies a strictly smaller cocycle exponent/scalar normalization theorem. Added the private proof imports and two new statement modules:

- `Sheaf.AlgebraicGeometry.ProjectiveSpace.PairwiseLaurentUnitExpansion`
- `Sheaf.AlgebraicGeometry.ProjectiveSpace.PairwiseCocycleNormalization`

The target node proof and proof dependencies now record this route.

## Proved and sorry left

Closed the original sorry in `exists_standardUnitCocycle_normalization_offDiagonal` (1 of 1). The delivery adds two strictly smaller named statements, each intentionally left as a theorem-level `sorry`:

- `exists_pairwise_laurent_unit_expansion` (`new-sfb-projective-pairwise-laurent-unit-expansion`), the distinct-overlap Laurent unit calculation.
- `exists_standardUnitCocycle_normalization_of_pairwise_laurent` (`new-sfb-projective-pairwise-cocycle-normalization`), the exponent and scalar coboundary calculation from those pairwise expansions.

No `sorry` occurs in a definition.

## No longer needed

No existing import was removed. The original target proof plan's direct dependency on the bundled Laurent calculation is replaced by the two new intermediate declarations; the transition-unit definitions remain needed. No declared dependency or module was pruned.

## Where the brief, the DAG or earlier work was wrong

The bundled theorem's proof plan hides two independent nontrivial arguments: classification of units on each higher-dimensional double overlap and the triple-overlap comparison of exponents and scalar coefficients. The existing library only contains the fully proved Laurent identification for the projective line, so neither higher-dimensional calculation is available as a reusable declaration. The target statement and all binders remain unchanged; the DAG node now records the two intermediate proof obligations.

## New nodes

`new-sfb-projective-pairwise-laurent-unit-expansion` records the pairwise Laurent unit expansion and is implemented by `Sheaf.AlgebraicGeometry.ProjectiveSpace.PairwiseLaurentUnitExpansion`.

`new-sfb-projective-pairwise-cocycle-normalization` records the triple-overlap exponent and scalar comparison and is implemented by `Sheaf.AlgebraicGeometry.ProjectiveSpace.PairwiseCocycleNormalization`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProjectiveSpace.PairwiseCocycleNormalization": "222eabfd1bcb697147a4621aa7cc570b7a7576e8", "Sheaf.AlgebraicGeometry.ProjectiveSpace.PairwiseLaurentUnitExpansion": "0a8c30a55cf91638fff82ff2b089259ea40f6fce", "Sheaf.AlgebraicGeometry.ProjectiveSpace.StandardUnitCocycleOffDiagonal": "0a3a642571bf32e42e2b4bd9a0023f641e5e0db2"}, "results": {}, "time": "2026-10-28T01:00:17+0800", "transitive": 0, "version": 1}
```

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
