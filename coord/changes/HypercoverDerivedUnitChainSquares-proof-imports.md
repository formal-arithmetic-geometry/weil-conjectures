# Sheaf.AlgebraicGeometry.HypercoverDerivedUnitChainSquares imports

## Reason

The proofs use the published source-library derived functors directly. The general
quasi-isomorphism-resolution construction and the two existential derived adjunction
and ringed-topos composition statements are unnecessary.

## Old

```lean
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
```

## New

These three import lines are removed. All declarations, statement signatures and
other public imports are unchanged. The public import removal drops re-exports of
the unused general resolution-construction API.

## Users

| module | group holding it | effect |
| --- | --- | --- |

There are no current direct Lean importers of the item module (checked by an exact
import-line search). Its DAG parents retain this node and its unchanged statement;
the module is not withdrawn. No consumer adaptations are needed.

## Status

landed 20261026T091058-L-3304495 2026-10-26 (merge of deliver/A6/Sheaf.AlgebraicGeometry.HypercoverDerivedUnitChainSquares)
