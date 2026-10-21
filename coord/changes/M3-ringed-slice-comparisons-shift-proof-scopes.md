# Sheaf.Paper.RingedSliceComparisonsShift proof scopes

## Reason

The new pure-tensor extensionality proof uses tensor notation from `MonoidalCategory`.
A local section supplies its site and coefficient variables, and another section holds
private generic shift lemmas. Preflight treats these commands as visible-command changes
and requires this record. All five existing public signatures, their definitions,
attributes, public imports and docstrings remain unchanged. Added declarations are
proved private helpers and the existing theorem proof; no new public API is introduced.

## Old

```lean
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
```

There was no `TensorExt` section.

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures MonoidalCategory
```

The private pure-tensor extensionality lemma is enclosed in `section TensorExt`, with
its explicit site and ring variables. Its variables end at `end TensorExt`.
The remaining new helpers have explicit parameters and are private.

## Users

`python3 tools/downstream.py Sheaf.Paper.RingedSliceComparisonsShift --names`
reports no current Lean importers. A direct import search in both source roots agrees.
The DAG attachment, parents and unit route are retained. No consumer adaptation is
required because public signatures, definitions, instances and imports are unchanged.
The new namespace opening changes name resolution only inside this file. None of the
five target statement meanings changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedSliceComparisonsShift | M3 | Proof namespace opening and private proof section; closes the sole hole. |

## Status

landed 20261021T160334-L-3591634 2026-10-21 (merge of deliver/M3/Sheaf.Paper.RingedSliceComparisonsShift)
