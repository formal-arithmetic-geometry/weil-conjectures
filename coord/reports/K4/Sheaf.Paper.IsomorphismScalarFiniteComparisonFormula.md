## What changed

The item theorem now combines two explicit stages: `finite_formula_unit_exists` supplies a finite comparison with the unit middle coefficient formula, and `finite_formula_of_unit` extends that formula by scalar linearity. Two new statement modules and their DAG nodes record these strictly simpler obligations. The item imports the extension module; the extension imports the unit module.

## Proved and sorry left

The original `finite_formula_exists` hole is closed by a real Lean proof combining the two named intermediate theorems. The delivery adds the split theorem `finite_formula_unit_exists` (node `lem-weil-isomorphism-scalar-finite-comparison-formula-unit`) and the split theorem `finite_formula_of_unit` (node `lem-weil-isomorphism-scalar-finite-comparison-formula-extension`), each with its proof intentionally postponed as a named theorem.

## No longer needed

No imports or existing DAG dependencies were removed. The original direct proof dependency is represented by the two split nodes, whose proof plans use `lem-weil-isomorphism-scalar-quotient-chain-squares`.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan omitted the necessary separation between the normalized unit pure-tensor calculation and its scalar-linearity extension. The concrete finite presentation is downstream of the generic quotient-chain comparison, so the wrapper cannot import the downstream `FiniteCore` module without an import cycle.

## New nodes

`lem-weil-isomorphism-scalar-finite-comparison-formula-unit` records the unit middle-coefficient calculation and is stated in `lean/Sheaf/Paper/IsomorphismScalarFiniteComparisonUnit.lean`.

`lem-weil-isomorphism-scalar-finite-comparison-formula-extension` records the scalar-linearity extension and is stated in `lean/Sheaf/Paper/IsomorphismScalarFiniteComparisonExtension.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IsomorphismScalarFiniteComparisonExtension": "991e1f8dbc18672728fbe44a766a492bec6ab242", "Sheaf.Paper.IsomorphismScalarFiniteComparisonFormula": "89226d90db73db521bd78b64177865a5f7ed5324", "Sheaf.Paper.IsomorphismScalarFiniteComparisonUnit": "4417f9977e578ee74703b0301cb54f9f56f18fa9"}, "results": {}, "time": "2026-10-28T08:08:43+0800", "transitive": 0, "version": 1}
```

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
