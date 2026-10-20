# Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange local elaboration commands

## Reason

The stage-3 preflight classifies added file-level attributes and elaboration options
as a change to what importers see and requires this record. The added commands are
local proof elaboration settings. They do not change any declaration signature,
definition body, public import, exported notation, instance, or target meaning.
The irreducibility hint prevents unintended unfolding of the tensor-pullback
construction during the new categorical proofs. The backward-elaboration options
allow the explicitly specified module and ring-sheaf coercions in those proofs.

## Old

The existing header fragment, verbatim:

```lean
noncomputable section

namespace AlgebraicGeometry.ConormalGradedAlgebra
```

There were no additional backward-elaboration options after `IsBaseChangeMap`.
The definitions `adjointPiece` and `IsBaseChangeMap`, and the complete signature of
`existsUnique_baseChangeMap`, are preserved verbatim in this delivery.

## New

The corresponding header fragment, verbatim:

```lean
noncomputable section

attribute [local irreducible] tensorPullback

namespace AlgebraicGeometry.ConormalGradedAlgebra
```

Added after the unchanged `IsBaseChangeMap` definition, verbatim:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Private helper lemmas additionally use `omit` to avoid unused section-instance
binders. These commands bind only the immediately following private theorem and
introduce no exported settings. No existing mathematical statement is changed.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange --uses
AlgebraicGeometry.ConormalGradedAlgebra.existsUnique_baseChangeMap` reports zero
current downstream modules and only the item module as a textual declaration use.
Unfinished DAG parents continue to depend on its unchanged full statement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange | F8 | Local proof elaboration only; public signatures and definitions unchanged |

No consumer adaptation is required, and no target statement is reopened: the
underlying definitions and the theorem signature are identical to the originals.

## Status

landed 20261020T211711-L-3490244 2026-10-20 (merge of deliver/F8/Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange)
