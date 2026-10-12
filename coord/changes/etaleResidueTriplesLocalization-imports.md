# etaleResidueTriples_colimit_localization imports

## Reason

The theorem and its proof do not use the filtered-category API. Remove the unused
public import; the declaration signature and all definitions remain unchanged.

## Old

```lean
public import Mathlib.CategoryTheory.Filtered.Basic
```

## New

The unused import is removed. No declaration changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.StrictHenselizationTriples | none recorded | It imports Filtered.Basic explicitly, so its statements and proofs retain that API. |

All downstream declarations have unchanged types and meanings; this removal does
not alter a definition used by a target and does not reopen target review.

## Status

landed 20261012T085225-L-8352 2026-10-12 (merge of deliver/D2/Sheaf.RingTheory.EtaleResidueTriplesLocalization)
