## What changed

The item theorem `WeilConjectures.RationalOperations.rationalHom_scalar_evaluation` is now proved by applying two strictly smaller categorical obligations. `RationalHomScalarCounitNormalization` defines the normalized closed counit and records the extension of `HomIdentification.integral_evaluation` to rational objects. `RationalHomScalarEvaluationCore` records the scalar square obtained from normalized counits and the existing `rationalHomScalar_transpose` theorem. The item imports the core module; the core imports the normalization module.

## Proved and sorry left

Closed 1 of 1 sorries in the item: `WeilConjectures.RationalOperations.rationalHom_scalar_evaluation`.

Added 2 split-off sorries:

- `WeilConjectures.RationalOperations.homIdentification_counit_normalized`, node `lem-sf-rational-hom-counit-normalized`.
- `WeilConjectures.RationalOperations.scalarEvaluation_of_normalizedCounits`, node `lem-sf-rational-hom-scalar-evaluation-core`.

The helper definition `WeilConjectures.RationalOperations.normalizedCounit` is fully defined, node `def-sf-rational-hom-normalized-counit`.

## No longer needed

The original DAG route's finite-free completed comparison and integral scalar-operation modules are not imported by the delivered proof. The proof uses `Sheaf.Paper.RationalHomScalarTranspose` and the two new helper modules, so the planned dependencies `lem-coef-finite-free-extension`, `lem-pur-integral-operations-scalar-extension`, and `lem-weil-finite-free-completed-scalar-comparison` are not needed by this item. No existing source module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan placed the full completed finite-free scalar construction directly in this theorem. The available library already has the abstract rational transpose compatibility theorem, so the direct theorem can be reduced to normalized-counit and transpose-core obligations. The statement is unchanged.

## New nodes

`def-sf-rational-hom-normalized-counit` records the concrete normalized counit definition.

`lem-sf-rational-hom-counit-normalized` records extension of the supplied integral evaluation normalization to all raw rational objects.

`lem-sf-rational-hom-scalar-evaluation-core` records the abstract scalar evaluation square from normalized counits and rational transpose compatibility.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalHomScalarCounitNormalization": "fb8ea93da25a8ea980da4939d174503452991821", "Sheaf.SixFunctors.RationalHomScalarEvaluation": "4f92c3e988d7a0336ab55a6085a6acb1d9860dc2", "Sheaf.SixFunctors.RationalHomScalarEvaluationCore": "85cd7fc86cc0d6b1a77d8a945304e39e1a3616d4"}, "results": {}, "time": "2026-10-28T06:55:57+0800", "transitive": 0, "version": 1}
```

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
