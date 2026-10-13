# AlgebraicGeometry.exists_ordinaryEvaluation_over_tensor_formula

## Reason

The proof assembles comparisons without needing to evaluate the construction of
`CategoryTheory.homComplexFunctor` or unfold the component definition of
`AlgebraicGeometry.IsSchemeOrdinaryEvaluation`. Keep these definitions closed
locally during elaboration. Their definitions, signatures and reducibility in
other modules are unchanged. The preflight conservatively classifies a changed
`attribute` command as an interface change and requires this record.

## Old

The main module had no local reducibility overrides for these definitions.
Its existing tensor instance registration was:

```lean
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
```

## New

The same instance registration remains. Before the main theorem, add exactly:

```lean
attribute [local irreducible] homComplexFunctor IsSchemeOrdinaryEvaluation
```

The attribute is local to this module. No declaration's signature or body is
changed by this command, and the main theorem's textual statement is identical.
The proof uses `backward.isDefEq.respectTransparency true` locally to respect
these boundaries. It compiles under the unchanged 60-second file limit.

## Users

The `downstream.py --uses AlgebraicGeometry.exists_ordinaryEvaluation_over_tensor_formula`
query found the following two textual users. No consuming module needs adaptation:
the changed attributes are local and the theorem has the same statement.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverComparisons | unclaimed | No interface or meaning change; consumes the same theorem. |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverTensorFormula | A4 | Proof elaboration keeps two large definitions closed. |

No target definition or target statement changes, and no target meaning review
is reopened by local elaboration attributes.

## Status

landed 20261013T224505-L-1469096 2026-10-13 (merge of deliver/A4/Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverTensorFormula)
