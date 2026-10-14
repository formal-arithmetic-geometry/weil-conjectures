# moduleCup_equal_derived_maps_class proof transparency

## Reason

Keep the expensive right-derived functor construction folded while elaborating the
comparison proof. This is a local proof-elaboration attribute, not a new mathematical
interface or changed data. The checker conservatively classifies attributes as
interface commands and therefore requires this record.

## Old

No local irreducibility attribute for `CategoryTheory.Functor.rightDerivedFunctor`
in `Sheaf.Paper.ModuleCupEqualDerivedMapsClass`.
The theorem proof was `by sorry`.

## New

```lean
attribute [local irreducible] Functor.rightDerivedFunctor
```

The theorem now obtains fixed comparison and tensor data and proves equality by
two single-resolution homology formulas. Its statement, universes, binders,
visibility, and all definitions and existing local instance bodies are unchanged.
The added private proof import is `Sheaf.Paper.ModuleCupSinglePairingHomology`.
The original public import of `ModuleCupResolutionRealization` is retained.
The local attribute expires at the end of this module and does not affect importers.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ModuleCupEqualDerivedMapsClass | T3 | Own proof only; local unfolding control. |
| Sheaf.Paper.ModuleCupRealizationEvaluation | unclaimed in supplied snapshot | Identical imported theorem signature; no adaptation. |

No downstream statement changes meaning. No definition or target statement is
changed. No forced adaptation is required.

## Status

landed 20261014T063823-L-2815637 2026-10-14 (merge of deliver/T3/Sheaf.Paper.ModuleCupEqualDerivedMapsClass)
