## What changed

Reworked the item into a short proof from two strict local reductions. The generic
sheaf-separatedness and scalar-commutation lemma is fully proved in
`SymmetricProjCrossTensorFromLocal`. The parent theorem applies it to the local
coefficient-chart statement in `SymmetricProjPullbackGeneratorLocalCoefficients`.
The latter is the only remaining mathematical hole and is strictly smaller: it
constructs one common-coefficient chart around each point and asserts no tensor
symmetry or gluing conclusion. The earlier unfinished chart helper was pruned,
and the unused q-prime-only split was withdrawn before delivery.

## Proved and sorry left

Closed the assigned hole:
`AlgebraicGeometry.SymmetricProjTautologicalCharts.normalized_pullback_generator_cross_tensor`.

Proved the new generic theorem
`AlgebraicGeometry.SymmetricProjTautologicalCharts.cross_tensor_of_local_coefficients_public`.

One sorry remains, in
`AlgebraicGeometry.SymmetricProjTautologicalCharts.normalized_pullback_generator_local_coefficients`.
No definition contains a sorry. One strictly simpler statement was split off.

## No longer needed

Removed the attempted private chart-normalization helpers and all imports used
only by them. The proof no longer needs the q-prime chart split or the old
absolute fraction-map search route. The parent now uses only the tensor-section
library and the two new local-reduction modules. No adopted source declaration
was changed or removed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt kept the full affine-chart construction in the parent file,
which caused deterministic kernel timeouts even after the local coefficient
calculation was isolated. The chart construction is a genuine intermediate
statement, so it is now represented explicitly as a single new DAG node. The
remaining parent proof is accepted by Lean in 7 seconds.

## New nodes

- `lem-trf-symmetric-proj-pullback-generator-local-coefficients`: local common-coefficient chart existence and formulas (one sorry).
- `lem-trf-symmetric-proj-cross-tensor-from-local`: generic local-to-global cross-tensor lemma (proved).

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.SymmetricProjCrossTensorFromLocal": "35421ff22f749ffcdb82f475c59cc99ac2ec7544", "Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorCrossTensor": "4503f928542082bcb66db28100eb2235be755bc3", "Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorLocalCoefficients": "d6c0ed75dd385cf32b5f9be4fd5aa0a9cd2d517d"}, "results": {"Sheaf.AlgebraicGeometry.SymmetricProjPullbackQuotientCrossTensor": {"hash": "5c6916dcd17d41398cf9c69dc74ada3e062d667a", "status": "OK"}}, "seconds": 15, "time": "2026-10-28T05:29:52+0800", "transitive": 0, "version": 1}
```

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
