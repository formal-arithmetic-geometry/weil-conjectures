# InternalModuleOperationsTransport local name scopes

## Reason

The private section-action helper and the direct-image comparison proof use monoidal
whiskering notation and pure tensors. The module therefore opens the monoidal category
namespace and the TensorProduct scope. Preflight classifies these public-section command
changes as requiring a change record. They add no declarations or instances and change
no existing statement or definition.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj
```

## New

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj TensorProduct
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | S6 | Names and notation used by proofs; existing declaration signatures and definitions are unchanged |

The changed commands only control name resolution within this module. No downstream
module needs adaptation, and no target statement changes meaning.

## Status

landed 20261019T005423-L-2767522 2026-10-19 (merge of deliver/S6/Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport)
