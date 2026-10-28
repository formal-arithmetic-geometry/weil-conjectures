# WeilConjectures.IteratedPurityScalarPasting.family_existsUnique

## Reason

The proof closes the existing unique-family hole. Its unused existential binder
is renamed from `V` to `_V` to avoid the unused-variable linter. This is an
alpha-renaming only: the proposition, all hypotheses, universes and visibility
are identical. No target statement or definition changes meaning.

## Old

```lean
theorem family_existsUnique : ∃! V : Family D C f d S I, True := by sorry
```

## New

```lean
theorem family_existsUnique : ∃! _V : Family D C f d S I, True := by
```

The new body constructs the family from the existing comparison-identification
witness and proves uniqueness of its localization, gamma, scalar and shift data.
All added helpers are private and completely proved; the four added imports are
private proof imports. Existing public imports and definitions are unchanged.

## Users

`python3 tools/downstream.py Sheaf.Paper.IteratedPurityScalarPasting --uses
WeilConjectures.IteratedPurityScalarPasting.family_existsUnique` reports zero
downstream modules and only the item's own module as a textual user.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IteratedPurityScalarPasting | D4 | One existing hole closed; proposition alpha-equivalent. |

No consumer needs adaptation and no other existing module is changed.

## Status

landed 20261028T081734-L-2775963 2026-10-28 (merge of deliver/D4/Sheaf.Paper.IteratedPurityScalarPasting)
