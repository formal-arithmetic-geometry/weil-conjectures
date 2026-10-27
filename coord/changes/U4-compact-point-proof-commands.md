# AlgebraicGeometry.Etale.CompactPointSource.compactPointSourceNormalization

## Reason

The proof needs names from `Opposite`, and three private helper calculations need scoped
elaboration options for canonical functor comparisons. The static interface checker records
these command changes even though every public signature, definition body and public import
is unchanged. All new helper definitions and theorems are private and fully proved.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
```

There were no scoped elaboration options or private helper declarations after `unitSection`.
The main theorem had the unchanged signature followed by `:= by sorry`.

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite
```

The `lowerStar_sections_normalization`, `ordinary_unit_sections` and
`unitSection_eq_pointSection` private helper theorems use the following scoped options:

```lean
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
```

The `ordinary_unit_sections` helper additionally uses:

```lean
set_option maxHeartbeats 50000 in
```

Each option is scoped to its own private theorem. The module adds the private concrete-to-abstract
augmentation equality and a composite natural transformation proving its naturality. These are
proof implementation details. The public statement and all public definition values are verbatim
unchanged, and the main theorem is fully proved. No target meaning changes.

## Users

`python3 tools/downstream.py Sheaf.Paper.CompactPointSourceNormalization` reports zero downstream
modules. The item is held by U4; no other module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactPointSourceNormalization | U4 | One hole closed; public interface unchanged. |

## Status

landed 20261024T020711-L-2648655 2026-10-24 (merge of deliver/U4/Sheaf.Paper.CompactPointSourceNormalization)
