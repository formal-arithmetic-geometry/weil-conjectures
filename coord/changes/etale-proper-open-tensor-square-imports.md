# AlgebraicGeometry.Etale.etaleProperOpenTensorSquare public imports

## Reason

The statement uses the existing constant-coefficient étale operations and their canonical
composition comparison. The general ringed-site monoidal-comparison theorem is not used
by either the statement or the completed proof. Remove its public import to prune this
unnecessary branch. Every existing declaration signature and definition stays unchanged.

## Old

```lean
public import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
```

## New

The above import is removed. All other existing public imports are retained.
The proof privately imports `Sheaf.AlgebraicGeometry.CompactificationProjectionComposition`
using `import all`, and applies its existing private `mixed_projection` theorem directly.
The imported module is unchanged. No declaration is copied or made public.
The duplicate private helper proofs in the returned packet are removed.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleProperOpenTensorSquare --uses
AlgebraicGeometry.Etale.etaleProperOpenTensorSquare` found zero downstream modules.
DAG parents continue to use the item; none is withdrawn or changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleProperOpenTensorSquare | E1 | Completed proof; unused public import removed; identical theorem signature. |

## Status

landed 20261024T014510-L-2207051 2026-10-24 (merge of deliver/E1/Sheaf.AlgebraicGeometry.EtaleProperOpenTensorSquare)
