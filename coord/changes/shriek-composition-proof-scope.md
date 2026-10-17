# ShriekComposition proof scope

## Reason

The new private proofs use the kernel, cokernel and zero-object API from
`CategoryTheory.Limits`. The file's existing `open` command includes that namespace.
Preflight classifies an edit of an `open` command as an interface change, so this record
makes the scope edit explicit. It changes name resolution inside this file only.
All existing declaration signatures, visibility and non-proof construction bodies remain
unchanged. The added imports are proof-only. The original long public import is wrapped
across two lines without changing its module or visibility.

## Old

```lean
open CategoryTheory
```

## New

```lean
open CategoryTheory Limits
```

## Users

`tools/downstream.py` lists the following five downstream modules. Neither exchange
isomorphism theorem is mentioned by name outside its own file. `Verdier` uses the existing
composition isomorphisms, whose signatures and construction bodies are unchanged. Opening a
namespace in this module does not open it in importers. No consumer adaptation is necessary;
no consumer is changed, irrespective of its current holder. No target statement or definition
used by a target changes, so no statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| `TargetsCheck` | maintainer | none; transitively imports unchanged interfaces |
| `WeilConjectures` | maintainer | none; transitively imports unchanged interfaces |
| `WeilConjectures.PoincareDuality.Poincare` | not consulted; no adaptation | none; transitively imports unchanged interfaces |
| `WeilConjectures.PoincareDuality.Verdier` | not consulted; no adaptation | none; uses unchanged composition isomorphisms |
| `WeilConjectures.TraceFormula.Basic` | not consulted; no adaptation | none; transitively imports unchanged interfaces |

The returned duplicate-helper defect is repaired without another interface edit:
`openUnitIsIso` is imported from `Sheaf.Paper.CondensedOpenClosedRecollement` with
`import all`, and the local duplicate is removed. The old direct proof import of
`Sheaf.Paper.ProfinitePointPullback` is redundant through that import and is removed.
No dependency module or consumer changes.

## Status

open
