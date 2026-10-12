# etaleResidueTriples_simple_root_stage

## Reason

The second reading removes a public import that only the proof needs. The filtered
API is already available to this proof from the proof-only colimit import. The sole
module importing this construction, Sheaf.RingTheory.EtaleResidueTriplesSimpleRoots,
has its own public import of Mathlib.CategoryTheory.Filtered.Basic, so it loses no
API or instance. No declaration signature, definition, or target meaning changes.

## Old

```lean
public import Mathlib.CategoryTheory.Filtered.Basic
```

## New

The explicit import is removed. Filtered.Basic remains available to the proof through:

```lean
import Sheaf.RingTheory.EtaleResidueTriplesColimit
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.EtaleResidueTriplesSimpleRootsConstruction | M1 | Proof-only filtered API remains available; signature unchanged. |
| Sheaf.RingTheory.EtaleResidueTriplesSimpleRoots | none (not adapted) | Imports Filtered.Basic independently; no change to its statement or proof. |

`tools/downstream.py --uses etaleResidueTriples_simple_root_stage` reports exactly
these two users. All 181 transitive downstream modules pass through the sole direct
importer, which independently imports the removed API, so their available filtered API
and the meanings of their statements remain unchanged.

The complete declaration signature in this delivery is byte for byte unchanged.
The import is absent from all public signatures here. No downstream target requires
another review of its meaning, since no definition or statement has changed.

## Status

landed 20261012T070543-L-3474052 2026-10-12 (merge of deliver/M1/Sheaf.RingTheory.EtaleResidueTriplesSimpleRootsConstruction)
