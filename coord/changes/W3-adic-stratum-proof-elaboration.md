# AlgebraicGeometry.Scheme.SfbAdicRestriction proof elaboration

## Reason

Preflight conservatively flags local attribute and namespace commands as an interface
change. These changes allow the actual completed coefficient limit cone and finite
comparison maps to elaborate in the new proofs. Every existing public declaration
signature, definition body, instance body, and public import is preserved. No source
library module is changed. New imports are proof-only. The new public theorems are
recorded by their two new DAG nodes.

## Old

The original file marks these definitions locally irreducible:

```lean
attribute [local irreducible] ConstantCompletion.completed ConstantCompletion.derivedPull
  HasDerivedCategory.standard
attribute [local irreducible] completedPull finiteComparison
```

## New

The first original attribute block is retained verbatim. The later block marking
`completedPull` and `finiteComparison` irreducible is removed. Before the coefficient
and finite-comparison proofs, respectively, the following local controls are added:

```lean
attribute [local semireducible] ConstantCompletion.completed
attribute [local semireducible] HasDerivedCategory.standard
```

All these attributes are local to the file's namespace. They change proof elaboration
only. Existing constructions and theorem statements are identical. New private helper
theorems and the private terminal-object helper definition are fully proved; no new
private helper or local command occurs in an existing public signature or definition.
No target-used definition changes meaning, and no target statement re-review is needed.

## Users

`python3 tools/downstream.py Sheaf.Paper.AdicStratumCompletionUnit --uses completedPull
finiteComparison` reports zero transitive Lean importers. Both names occur only in the
item itself. DAG parents with unfinished proofs retain the unchanged public API and the
original unit route; no withdrawal is requested. No consumer requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicStratumCompletionUnit | W3 | Original API unchanged; proof elaboration controls only. |
| Sheaf.Paper.AdicStratumCoverConservativity | W3, new | Proved generic conservativity theorem; new node. |
| Sheaf.Paper.ExactCompletedKoszulPullback | W3, new | Separate transport theorem; documented new hole and node. |

## Status

landed 20261021T160738-L-3834799 2026-10-21 (merge of deliver/W3/Sheaf.Paper.AdicStratumCompletionUnit)
