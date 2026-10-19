# Sheaf.Paper.IndHeartKernelsCokernels.ZeroObjectScope

## Reason

The proof constructs the zero-source square in the constructible category and needs the
`ZeroObject` scoped notation for its zero object and zero morphisms. The scope is exported
by the module's existing public section, so this required stage-3 change record.

## Old

```lean
open scoped CategoryTheory.Obj
```

## New

```lean
open scoped CategoryTheory.Obj ZeroObject
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IndHeartKernelsCokernels | M3 | Uses zero-object notation in its private square-finality proof. |

## Status

landed 20261019T005342-L-2755976 2026-10-19 (merge of deliver/M3/Sheaf.Paper.IndHeartKernelsCokernels)
