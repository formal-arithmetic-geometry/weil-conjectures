# AlgebraicGeometry.Scheme.constantAdicQuotientRealization_reflects_iso_of_map

## Reason

Fill the existing proof without new holes and record its actual route. The item's
statement-dependency list also contains a nonexistent scalar-comparison node id;
correct that reference to the node which already realizes the imported module.
There is no change to the mathematical statement, elaborated Lean signature,
definitions, public imports, or public instances.

## Old

The item's `stmt_deps` was:

```json
[
 "lem-sfb-constant-realization-reflects-isomorphism",
 "def-weil-pbc-constant-adic-quotient-scalar-comparison"
]
```

The existing theorem's proof was `by sorry`.

## New

The item's `stmt_deps` is:

```json
[
 "lem-sfb-constant-realization-reflects-isomorphism",
 "lem-weil-pbc-constant-adic-quotient-scalar-comparison"
]
```

The unchanged theorem is proved by faithful exact ordinary realization and the
unbounded homology isomorphism criterion. Its proof-only imports and DAG
`proof`, `proof_deps`, and `proof_origin` record the actual comparisons.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ConstantAdicQuotientRealizationReflectsIsoOfMap` | E9 | Own proof closed; DAG reference corrected. |
| `Sheaf.Paper.ConstantAdicQuotientRealizationIsoLift` | unclaimed in shared snapshot | Direct importer; unchanged interface and proof application. No adaptation required. |

All indirect consumers retain the same declaration and elaborated type. No
source-library file or other existing Lean module is changed.

## Status

landed 20261028T055643-L-788871 2026-10-28 (merge of deliver/E9/Sheaf.Paper.ConstantAdicQuotientRealizationReflectsIsoOfMap)
