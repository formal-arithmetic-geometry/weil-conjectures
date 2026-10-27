## What changed

Proved the main theorem by extracting cohomological bounds and applying finite-ring derived local constancy. Added the local finite-model comparison module and imported it as the single proof dependency.

## Proved and sorry left

The declaration `AlgebraicGeometry.Scheme.derivedHomSheafComparison_isIso_lisse` is proved. One strictly simpler intermediate theorem remains sorry: `AlgebraicGeometry.Scheme.derivedHomSheafComparison_isIso_of_finite_local_models` in node `lem-weil-pbc-derived-hom-sheaf-comparison-lisse-local-model`.

## No longer needed

The original proof plan's direct imports for the bounded-free model, K-injective restriction, global sections, Noetherian criterion, and finite-level comparison are encapsulated by the split local-model theorem and are not imported by the main module directly.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof expanded the entire local RHom calculation in the item. The existing finite-ring local-constancy theorem already packages the cover and finite complexes, so the remaining argument is a single strictly simpler local-model theorem.

## New nodes

`lem-weil-pbc-derived-hom-sheaf-comparison-lisse-local-model` records the local bounded finite-model RHom comparison and descent, with its proof postponed for a separate worker.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.DerivedHomSheafComparisonLisse": "bb578cf1e103420900bd565abc3df51c8ec610da", "Sheaf.AlgebraicGeometry.DerivedHomSheafComparisonLisseLocalModel": "d5a4971077cb12bbd57826dee326d953de1fe7e2"}, "results": {}, "time": "2026-10-27T23:47:35+0800", "transitive": 0, "version": 1}
```

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
