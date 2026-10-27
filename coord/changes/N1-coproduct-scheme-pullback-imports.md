# CoproductSchemePullback imports

## Reason

The theorem uses the fppf partition data and standard scheme and presheaf APIs.
Its statement does not use algebraic spaces or the scheme coproduct construction.
Remove the unused algebraic-space import and make the scheme Limits import private
to the proof. This avoids exposing unrelated definitions and proof dependencies.

## Old

```lean
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Gluing
```

## New

```lean
public import Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Gluing
```

The existing public theorem's signature and docstring are unchanged. All added
helpers are private and proved. No public definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| No current downstream Lean modules | none | No consumer adaptation is needed. |

`tools/downstream.py Sheaf.AlgebraicGeometry.CoproductSchemePullback --uses
fppfSheaf_coproduct_scheme_pullback` reports zero downstream modules and only the
item's declaration. Text search also found no importers in the quarantined source
trees. The DAG parents remain needed and retain the unchanged theorem interface.
No target statement or definition changes, so target statement review does not reopen.

## Status

landed 20261023T123911-L-1288838 2026-10-23 (merge of deliver/N1/Sheaf.AlgebraicGeometry.CoproductSchemePullback)
