# Sheaf.SixFunctors.FlatModelGeneration proof namespace opening

## Reason

The new pro-etale proofs use `ObjectProperty.IsTriangulated` and related names from
`CategoryTheory.Pretriangulated`. The module-level `open` command adds that namespace.
Delivery preflight classifies a changed `open` command as a visible-command change and
requires this record. This is a name-resolution change within the item, not a change to
any existing declaration signature, definition, attribute or public import.

The other additions are proved private helpers and private proof imports. They establish
the coefficient, flatness, stalk and derived-comparison bridges needed to close all three
pro-etale holes. Existing public declarations and their universes remain verbatim.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
```

## New

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
```

## Users

`python3 tools/downstream.py Sheaf.SixFunctors.FlatModelGeneration --names` reports
no current Lean importers. The item's DAG attachment and parent obligations are preserved.
No consumer adaptation is required: all existing public declaration signatures, definitions
and public imports are unchanged, and the namespace opening affects only elaboration in
this file. Target statement meanings are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.FlatModelGeneration | A2 | Adds proof namespace opening; closes 3 holes. |

## Status

landed 20261021T020049-L-2580122 2026-10-21 (merge of deliver/A2/Sheaf.SixFunctors.FlatModelGeneration)
