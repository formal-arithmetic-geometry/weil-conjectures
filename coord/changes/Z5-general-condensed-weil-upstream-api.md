# WeilConjectures.GeneralCondensedWeil.Target

## Reason

Restore the assigned quarantined module from its coord/rework.tsv archive. The
recorded error is the removed upstream name WeilBoundedConstructibleOfEnd, followed
by cascading unknown Target errors. The current upstream name
WeilBoundedConstructible denotes precisely IsoAlgebra of the bounded constructible
pullback along an endomorphism. This is the same category required by the node;
there is no automorphism or finite-order assumption added to modelFrobenius.

## Old

The active module is absent. The archived definition, verbatim, is:

```lean
abbrev Target := WeilBoundedConstructibleOfEnd l (modelFrobenius D Y₀)
```

Its original public imports include WeilConjectures.TraceFormula.Statement.

## New

```lean
abbrev Target := WeilBoundedConstructible l (modelFrobenius D Y₀)
```

Retain every archived public and private import and add the public imports
WeilConjectures.TraceFormula.CompactCohomology and
WeilConjectures.TraceFormula.Stalk. These expose the actual globalOperator and
stalkFrobenius that occur in the public Data fields under the current module API.
No operator is replaced by an independently chosen map. All other archived
signatures and definition bodies are retained verbatim, including the theorem.
The node's Lean attachment is retained and its note records this restoration.
No source-library file is changed and no target statement changes meaning.

## Users

The initial downstream query reports unknown module because the active source is
quarantined. Repeating with the supported --allow-missing option finds zero
modules downstream, and zero uses of Target or Data. A search of both active Lean
roots and the quarantine Lean tree finds no imports of this module and no uses of
GeneralCondensedWeil declarations outside the archive itself. Thus no consumer
adaptation is needed. The DAG parent lem-zl-finite-stage-categorical-trace still
needs this node; its dependency and the item's full planned dependencies are kept.
Zero importers is not used as a justification for withdrawal.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.GeneralCondensedWeilRealization | Z5 (dispatcher assignment) | Restore archive and repair Target API name and public operator imports. |

## Status

landed 20261025T124526-L-2053502 2026-10-25 (merge of deliver/Z5/Sheaf.Paper.GeneralCondensedWeilRealization)
