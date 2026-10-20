# AlgebraicGeometry.Scheme.bottomFreeChain_pullback_square

## Reason

Restore the module listed in coord/rework.tsv from its quarantine archive. The
archived public derived-pullback import points to a retired Sheaf module. The
current upstream module provides the definitions used by the unchanged theorem.
This repairs the sync breakage; neither a definition nor a statement is changed.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.BottomFreeChainPullbackSquare | X3 | Restored from quarantine with its complete proof; compiles against the upstream import. |
| Sheaf.AlgebraicGeometry.ZeroBottomArrowPullbackLocal | quarantined; not adapted | Its archived call uses the same theorem signature. Its own retired derived-pullback import is a separate restoration item. |

The live downstream.py query reports an unknown module because the item is
currently quarantined. A source search of lean/ and quarantine/ finds precisely
the consumer above. The parent node lem-sc-zero-bottom-arrow-pullback-local still
uses this node in proof step 3 and proof_deps; both attachments are preserved.
No target or definition changes meaning, and no consumer adaptation is required.

## Status

landed 20261020T233236-L-910312 2026-10-20 (merge of deliver/X3/Sheaf.AlgebraicGeometry.BottomFreeChainPullbackSquare)
