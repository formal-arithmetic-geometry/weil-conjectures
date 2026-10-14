# pinnedTensorSquareCompatibilityT2Instance3

## Reason
The sandbox module is compiled alongside an existing compiled copy of the target module, so the local instance declaration name must be unique during isolated compilation. This preserves the instance type and behavior exactly.

## Old
```lean
local instance pinnedTensorSquareCompatibilityInstance3
    (Y : Scheme.{u}) : (curriedTensor Y.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor Y.sheaf
```

## New
```lean
local instance pinnedTensorSquareCompatibilityT2Instance3
    (Y : Scheme.{u}) : (curriedTensor Y.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor Y.sheaf
```

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PinnedTensorSquareCompatibility | T2 | local proof instance name only |

## Status
landed 20261014T013045-L-3417693 2026-10-14 (merge of deliver/T2/Sheaf.AlgebraicGeometry.PinnedTensorSquareCompatibility)
