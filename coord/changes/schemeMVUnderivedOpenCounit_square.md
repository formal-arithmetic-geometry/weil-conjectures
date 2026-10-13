# schemeMVUnderivedOpenCounit_square

## Reason

Replace the returned duplicate quotient-representative helper by a genuine
ordinary-module reduction. The existing theorem's signature and meaning are
unchanged. The new public ordinary helper lives in its own new module, imported
only for the proof. A proved private helper performs degreewise quotient descent.

## Old

The existing theorem statement with proof by sorry; the returned version instead
applied underived_open_counit_square_on_quotient after quotient-object surjectivity.

## New

The identical existing theorem statement, proved by lift_open_counit_square
specialized to the open adjunctions and fixed underived comparison models,
using schemeMVOrdinaryOpenCounit_square in every degree. The ordinary helper
remains by sorry and has its own node and complete natural-language proof.
No existing public signature, definition or visibility changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedMayerVietorisOpenCompositionCounit | unclaimed | unchanged statement; uses the same theorem |

## Status

landed 20261013T222422-L-1229689 2026-10-13 (merge of deliver/W2/Sheaf.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare)
