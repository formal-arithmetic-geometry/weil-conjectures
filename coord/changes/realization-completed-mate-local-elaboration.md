# AlgebraicGeometry.Scheme.realizationCompletedMate

## Reason

Preflight classifies new file-level attribute commands as an interface change. The proof
requires local irreducibility controls to prevent expansion of valuation-ring data and chosen
derived functors during elaboration. Without the private assembly helpers the full theorem
kernel check timed out; with them the whole file compiles cleanly in 14.5 seconds. These
attributes are all local: importers receive the same public theorem and public imports.
No global attribute, mathematical definition, binder, universe, or theorem statement changes.
The additional `backward.isDefEq.respectTransparency.types` option affects elaboration only.

## Old

Existing elaboration commands, verbatim:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
```

There were no `attribute [local irreducible]` commands in the item module.
The theorem signature is unchanged verbatim in the delivery.

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [local irreducible] HasDerivedCategory.standard
```

Inside the existing namespace, after the valuation-ring calculation:

```lean
attribute [local irreducible] pbcPadicCoefficientDatum integralConstantDerived
  cbcDatumOrdinaryTransport pbcActualDerivedPullCompIso
  integralConstantDerivedPullIso
```

After the unit-invertibility helper:

```lean
attribute [local irreducible] AdicCoefficientDatum.ordinaryToCompleted
  AdicCoefficientDatum.completedExchange
```

All additional declarations are proved private helpers, with no new public signature.
No heartbeat or timeout limit is changed.

## Users

`tools/downstream.py Sheaf.Paper.RealizationCompletedMate --uses realizationCompletedMate`
reports zero downstream modules and only the item itself as a textual user. Unfinished DAG
parents remain supported: this packet preserves the public signature and visibility exactly.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.RealizationCompletedMate | F6 | Proof filled; private helpers and local elaboration controls. |

No consumer needs adaptation. The item compiles against its original imports plus the added
private proof imports. The imported declarations' signatures and bodies are untouched.

## Status

landed 20261023T231136-L-3551729 2026-10-23 (merge of deliver/F6/Sheaf.Paper.RealizationCompletedMate)
