# AlgebraicGeometry.Scheme.Modules.exists_unique_qcoherentNormalizedComparison

## Reason

Restore the module quarantined by upstream sync `5f7b33eac`, as assigned in
`coord/rework.tsv` and the rework queue of 2026-10-20. Its private import of
`WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization`
imports the new upstream naturality module, while the public canonical comparison
interface imports the existing `Sheaf` naturality module. These two modules define
the same names. The recorded global error reports an environment collision at
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.moduleComparisonEquiv`.

The normalization module supplies no identifier used by the archived item.
Remove that private import. This fixes an actual import failure; it does not
claim a proof of the theorem's existing hole.

## Old

The archived file includes this proof-only import:

```lean
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization
```

Its public imports and the complete theorem statement and body are otherwise
exactly those in the quarantine archive.

## New

The above private import is absent. Every other byte of the archived Lean file
is retained, including all public imports, the theorem statement, its docstring,
and its existing `:= by sorry` body. There is no changed definition or statement.
The node's Lean attachment, planned proof and dependencies are preserved.

Validation: `lcompile.py --all` compiles the restored sandbox module in 5.8 s
against the published server library. There is one named theorem hole before
and after restoration and no added hole.

## Users

`tools/downstream.py` cannot index the item because its library path is currently
quarantined. A textual scan of both library roots and the quarantined algebraic
geometry modules finds the following sole direct importer. A scan of DAG node
references finds the corresponding pullback node as the sole parent.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison | J1 | Restore archived module, removing one conflicting private import. |
| Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback | unclaimed | Public interface is identical; no adaptation. Still depends on the separately quarantined QcoherentNormalizedPullbackSquare, held by J2. |

No other group's module is changed. No source-library declaration is edited,
removed or replaced with a hole. No target or definition used by a target changes.

## Status

landed 20261020T150645-L-2555310 2026-10-20 (merge of deliver/J1/Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison)
