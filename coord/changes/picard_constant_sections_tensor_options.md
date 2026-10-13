# AlgebraicGeometry.Scheme.Modules.exists_picard_constant_sections_tensor_basis

## Reason

The two transparency settings support elaboration of the proof. Existing declaration signatures and public definition bodies remain unchanged.

## Old

```lean
set_option autoImplicit false
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardConstantSectionsTensor | A3 | Elaboration only; public signatures and definition bodies unchanged. |

No downstream module is adapted: these local elaboration settings do not change the public interface.

## Status

landed 20261013T150349-L-808638 2026-10-13 (merge of deliver/A3/Sheaf.AlgebraicGeometry.PicardConstantSectionsTensor)
