# pinnedTensorSquareCompatibilityT2Instance1

## Reason
The sandbox module is compiled alongside an existing compiled copy of the target module, so the local instance declaration name must be unique during isolated compilation. This preserves the instance type and behavior exactly.

## Old
```lean
local instance pinnedTensorSquareCompatibilityInstance1 (Y : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  pullbackDescentModuleTensor Y
```

## New
```lean
local instance pinnedTensorSquareCompatibilityT2Instance1 (Y : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  pullbackDescentModuleTensor Y
```

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PinnedTensorSquareCompatibility | T2 | local proof instance name only |

## Status
landed 20261014T013045-L-3417693 2026-10-14 (merge of deliver/T2/Sheaf.AlgebraicGeometry.PinnedTensorSquareCompatibility)
