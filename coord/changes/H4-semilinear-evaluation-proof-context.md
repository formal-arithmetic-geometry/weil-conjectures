# AlgebraicGeometry.ProEtale.SemilinearProperOpen.semilinearEvaluationDerivedAdjunction

## Reason

The proof needs exact-composition instances and must keep chosen adjoint and localization
models folded while comparing their canonical maps. The static delivery gate conservatively
classifies added `section`/`attribute` commands as an interface change and requires this
record. Every added attribute is explicitly `local`; no exported attribute, instance,
notation, definition body, public import, or existing signature changes.

## Old

The file had no local exact-composition registrations or local irreducibility commands.
Its original proof was verbatim:

```lean
:= by
  sorry
```

## New

The proof is complete. The following proof-context commands are added verbatim:

```lean
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf
```

That section ends before the original variable command and definitions. Before the new
concrete private proof helpers, the file adds:

```lean
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf
  evalPullInv
```

The two local backward-elaboration transparency options allow converting the existing
system-category aliases. Two tactic-linter replay options avoid replaying expensive
dependent conversions; kernel checking remains active. None is exported to importers.
All seven existing comparison definitions and the complete theorem signature stay verbatim.
New helpers are private proved theorems only.

## Users

`python3 tools/downstream.py Sheaf.SixFunctors.SemilinearEvaluationDerivedAdjunction`
reports zero current Lean downstream modules. The item remains required by unfinished DAG
parents; no withdrawal is proposed and all parent dependencies are retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.SemilinearEvaluationDerivedAdjunction | H4 | Replaces its one hole with a complete proof; local elaboration context only. |

There are no adapted modules. Future consumers see the same definitions, theorem type,
public imports, and instance interface. No target definition or statement changes.

## Status

landed 20261023T231328-L-3577274 2026-10-23 (merge of deliver/H4/Sheaf.SixFunctors.SemilinearEvaluationDerivedAdjunction)
