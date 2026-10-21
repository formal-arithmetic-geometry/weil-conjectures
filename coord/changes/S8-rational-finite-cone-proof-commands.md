# AlgebraicGeometry.Scheme.RationalConeModels proof section commands

## Reason

Stage-3 preflight classifies added section commands as changing what importers
see and requires this record. The module opens tensor notation to write its
private denominator helpers and uses `omit` to exclude unused geometric section
hypotheses from private helper signatures. No existing statement, definition,
instance, public import, namespace, or attribute is changed. Every added helper
is private and proved. This records the command change explicitly for review.

## Old

```lean
open scoped ZeroObject
```

The original file has no `omit` commands for the new private helpers.

## New

```lean
open scoped ZeroObject TensorProduct
```

The following command prefixes the new private helpers
`finite_construction_step`, `finite_construction_generator`,
`finite_construction_mono`, and `truncation_step`:

```lean
omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] in
```

Existing public signatures and their geometric hypotheses stay verbatim. These
commands affect notation and private-helper elaboration within this module;
no target interpretation changes and no consumer adaptation is needed.

## Users

`tools/downstream.py Sheaf.Paper.RationalRealizationFiniteConeModels --uses
AlgebraicGeometry.Scheme.RationalConeModels.bounded_model` reports zero downstream
modules and one use in the item itself.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalRealizationFiniteConeModels | S8 | All six theorem holes proved; tensor notation and private-helper section commands added. |

No other module is adapted. No target definition or statement changes, so no
statement review is reopened by these proof commands.

## Status

landed 20261021T190641-L-3711670 2026-10-21 (merge of deliver/S8/Sheaf.Paper.RationalRealizationFiniteConeModels)
