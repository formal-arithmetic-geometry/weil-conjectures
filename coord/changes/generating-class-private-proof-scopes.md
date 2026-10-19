# CategoryTheory.GeneratingClassCounterexample private proof scopes

## Reason

The stage-3 interface scanner flags the added `omit ... in` commands used for private
proof helpers. They remove an unused derived-category section instance from these private
theorems. They do not alter any existing public declaration, definition, instance, notation,
visibility, or public import. The counterexample theorem retains exactly its original
signature. This record documents the conservative command-level interface flag.

## Old

The existing section instance is:

```lean
variable [HasDerivedCategory.{w} (ModuleCat.{0} Ring)]
```

There were no private model, connection, quotient or shear helpers, and no `omit` commands.
The public counterexample theorem ended in `:= by sorry`.

## New

The existing section instance and every existing signature are unchanged. Private theorems
`modelD_sq`, `model_ge`, `model_le`, `model_terms`, `model_diff`, `delta_leibniz`,
`modelConnection_leibniz` and `quotient_one_ne_zero` are scoped with the exact command:

```lean
omit [HasDerivedCategory.{w} (ModuleCat.{0} Ring)] in
```

Its scope is the immediately following private theorem. The new public theorems are in
the separate modules PerfectDerivationTransformation and TwoTermSelfExtensionHom and are
attached to new DAG nodes. Their imports in the item are proof-only.

## Users

`tools/downstream.py` with `--uses` for the existing counterexample declaration found no
external module mentioning it; its own source is the only textual match. The private
helpers have no external users. All 399 downstream importers retain the same public
interface and need no adaptation. No target statement or definition used in a target
statement changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Triangulated.GeneratingClassDetermination | Q1 | Proof completed; private theorem scopes added; existing public signatures unchanged. |

## Status

landed 20261019T005401-L-2761936 2026-10-19 (merge of deliver/Q1/Sheaf.CategoryTheory.Triangulated.GeneratingClassDetermination)
