# comparisonPullbackOpenUnit

## Reason

The proof uses two proved private helpers and scoped elaboration options to compare
canonical localization adjunctions. The interface scanner records the option commands.
This record documents their scope; every existing public signature and definition,
public import, namespace and file-level option is unchanged.

## Old

`comparisonPullbackOpenUnit` had its existing signature and proof `:= by sorry`.
There were no private helper declarations or scoped options in this module.

## New

`comparisonPullbackOpenUnit` has the same signature and a complete proof.
The two new private lemmas `comparisonPullbackOpenUnit_conjugate` and
`comparisonPullbackOpenUnit_directImage_mate` each use only these scoped options:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
```

The options end with the helper declaration. Added one proof-only import of
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique`; removed six redundant
proof-only imports listed in report.md. The three public abbreviation bodies and
all existing theorem and abbreviation signatures are unchanged.

## Users

Ran `python3 tools/downstream.py Sheaf.AlgebraicGeometry.ComparisonPullbackOpenUnit
--uses comparisonPullbackOpenUnit`: 161 downstream modules, and the only textual
user of the theorem name is the item itself. All downstream consumers see identical
public signatures, definitions and imports; no adaptation is necessary and no target
meaning changes. Only the following module is delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ComparisonPullbackOpenUnit | H8 | Proof and private helpers only. |

## Status

landed 20261019T093442-L-2313044 2026-10-19 (merge of deliver/H8/Sheaf.AlgebraicGeometry.ComparisonPullbackOpenUnit)
