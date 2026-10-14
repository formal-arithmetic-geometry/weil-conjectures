# moduleCup_equal_derived_maps_class proof transparency

## Reason

Keep the expensive right-derived functor construction folded while elaborating the
comparison proof. This attribute is local to the item and changes no mathematical data,
statement, instance body, or imported behavior. The delivery checker may classify local
attributes conservatively as interface commands.

## Old

The item had no local irreducibility attribute for
`CategoryTheory.Functor.rightDerivedFunctor`. Its theorem proof was `by sorry`.

## New

```lean
attribute [local irreducible] Functor.rightDerivedFunctor
```

The theorem has a complete proof from the fully proved one-pair formula. Its exact
signature and all existing instance definitions remain unchanged. The heartbeat setting
is a proof-elaboration budget; the file timeout remains 60 seconds.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ModuleCupEqualDerivedMapsClass | E2 | Local unfolding control only. |
| Sheaf.Paper.ModuleCupRealizationEvaluation | unclaimed in supplied snapshot | Same imported theorem and exported interface; no adaptation. |

The `tools/downstream.py --uses moduleCup_equal_derived_maps_class` output names these two
modules as direct declaration users. Its 193-module import closure sees exactly the same
exported declaration. The local attribute expires at the end of the item module. No user
requires adaptation and no target statement changes meaning.

## Status

landed 20261014T152404-L-1128224 2026-10-14 (merge of deliver/E2/Sheaf.Paper.ModuleCupEqualDerivedMapsClass)
