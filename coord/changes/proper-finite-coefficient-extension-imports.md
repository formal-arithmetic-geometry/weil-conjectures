# Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension

## Reason
The assigned theorem now delegates its two comparison clauses to a new core theorem so
that the independently proved mate normalization remains in the item module. The original
public imports are retained by the core module, which is publicly imported by the item.
This preserves the declarations visible to existing consumers while keeping the item header
small.

## Old
The item module directly publicly imported the projection, tensor/pullback, derived category,
properness and finite-type modules, and directly imported the proof-only comparison modules.

## New
`Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtensionCore` publicly imports the original
statement dependencies and privately imports the proof dependencies. The item publicly
imports only this core module; all original declarations remain available transitively.
No theorem signature or declaration visibility changed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension | F1 | Updated to use the core theorem and retain the original target signature. |

## Status

landed 20261020T233133-L-898201 2026-10-20 (merge of deliver/F1/Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension)
