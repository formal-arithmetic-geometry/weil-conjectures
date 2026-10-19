# Sheaf.AlgebraicGeometry.ArtinSchreierPrimeCharacterComparison elaboration controls

## Reason

The proof adds local elaboration commands (`omit`, `set_option`, and a local
irreducibility attribute) around private helper lemmas. The stage-3 interface
scanner conservatively classifies these commands as changes to what the module
makes visible. They are scoped to this module and do not alter any public
declaration, definition, instance, notation, or target statement. The controls
are needed to elaborate the dependent sheaf comparisons within the file timeout.

## Old

The module had no local irreducibility attribute and no helper-scoped heartbeat
or transparency options:

```lean
set_option autoImplicit false
```

The proof imported the finite-etale splitting, finite exchange, finite stalk,
and finite trace modules directly.

## New

The module retains `set_option autoImplicit false` and adds only scoped controls:

```lean
attribute [local irreducible] artinSchreierFunctionCover
  artinSchreierFunctionProjection artinSchreierBaseConstants
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
private lemma comparison_fixed_images := by
  ...
```

The same scoped options are used for `comparison_geometric`; `omit [CharZero L]`
is used only on private helper lemmas whose statements do not require that
instance. The removed modules remain available transitively through the retained
public imports where needed; no public import was changed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ArtinSchreierPrimeCharacterComparison | F8 | Local elaboration controls and proof-only import pruning; public declarations and signatures are unchanged. |

No other module imports this item directly in the current library. No consumer
is adapted.

## Status

landed 20261019T231153-L-557158 2026-10-19 (merge of deliver/F8/Sheaf.AlgebraicGeometry.ArtinSchreierPrimeCharacterComparison)
