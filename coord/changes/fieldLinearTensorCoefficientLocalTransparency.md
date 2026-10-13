# AlgebraicGeometry.Scheme.Modules.scalarTensorCoefficient

## Reason

The new proof of `exists_scalarTensorCoefficient` needs the coefficient definition kept
folded during type inference. Without the local attribute, the unchanged characterization
signature exceeds 200000 elaboration heartbeats at `whnf`. With it, the complete module
compiles. The static interface check conservatively treats this local command as an
interface change. The attribute is local to this section and is not exported.
All global attributes retain their original placement. No signature or definition body
changes, and no target meaning changes or target statement review is reopened.

## Old

No local reducibility attribute on `scalarTensorCoefficient`.
The definition and existing global commands are unchanged.

## New

```lean
attribute [local irreducible] scalarTensorCoefficient
```

This command occurs after the definition and before the private tensor comparison helper.
The proof explicitly unfolds the coefficient where its construction is needed.

## Users

A read-only `tools/downstream.py` search with `--uses scalarTensorCoefficient` found the
item and the following downstream textual user. This command changes neither the exported
reducibility of the definition nor its data. No adaptations are necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations | H3 | Local proof elaboration only. |
| Sheaf.AlgebraicGeometry.ExternalCupScalarBalance | unclaimed | Unaffected; local attribute is not exported. |

## Status

landed 20261013T054220-L-443657 2026-10-13 (merge of deliver/H3/Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations)
