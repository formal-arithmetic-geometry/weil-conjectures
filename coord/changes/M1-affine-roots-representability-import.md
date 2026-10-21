# AlgebraicGeometry.affineRoots_representability

## Reason

The proof constructs the presheaf isomorphism directly from the kernel defining the
roots sheaf. The separate representable-presheaf sheaf theorem is unnecessary.
Remove its public import; all three existing public signatures and both definitions
are unchanged. There are no current direct or transitive Lean importers of the item.
The DAG parents still require this item, which is retained and proved in full.

## Old

```lean
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
```

## New

```lean
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineRootsRepresentability | M1 | Own proof compiles without the import. |

No other Lean module imports the item or mentions any of its three public declarations.
No consumer adaptation is required. The pending DAG consumers keep the same statement.

## Status

landed 20261021T061503-L-1781548 2026-10-21 (merge of deliver/M1/Sheaf.AlgebraicGeometry.AffineRootsRepresentability)
