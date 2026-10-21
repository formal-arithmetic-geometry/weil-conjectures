# SheafOfModules.flat_coefficient_reduction_adjunct proof context

## Reason

The proof uses tensor notation, the existing independent-coefficient monoidal instances,
and more transparent elaboration of the homotopy quotient. Preflight classifies these
file-level commands as an interface change, so this record documents them explicitly.
All existing public declarations, definition bodies and public imports are unchanged.
The added instance attributes are local to the file; the options affect elaboration only.
No target meaning changes and no consumer adaptation is necessary.

## Old

The original file has no additional commands between the comparison structure and the
final theorem. Its existing options, namespace and variables are retained verbatim.

## New

The proof context before the new private helpers is:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.MonoidalCategory
attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
```

The two transparency options are repeated before `reductionMap`. Every new helper in
this item module is private and proved. The new ordinary comparison module separately
exports its proved theorem and carries its own DAG node.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FlatCoefficientReductionAdjunct | G2 | Proof support only; existing interface unchanged. |
| Sheaf.Algebra.Homology.OrdinaryFlatCoefficientComparison | G2 (new module) | Proved ordinary comparison imported privately by the item. |

Source search finds no Lean importer or external declaration user of the item module.
Unfinished DAG parents retain the same attachment and unchanged comparison interface.
The local attributes do not register any instance for importing files.

## Status

landed 20261021T111128-L-4164610 2026-10-21 (merge of deliver/G2/Sheaf.Algebra.Homology.FlatCoefficientReductionAdjunct)
