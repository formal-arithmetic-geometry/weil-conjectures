# WeilConjectures.ConcreteIntegralProjection.finiteArrow

## Reason

Write the identical endpoints explicitly to avoid inferring them through large functor constructions. The map and its meaning are unchanged by definitional equality; no consumer is adapted. The structure fields still contain precisely the source, target, and arrow of finiteReductionProjection. Target meanings are unchanged; the independent review can check the displayed constructions.

## Old

```lean
def finiteArrow
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    Arrow (proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1))) :=
  Arrow.mk (finiteReductionProjection l E n c
    ((scalarReductionDerivedExtension l E X n).obj K)
    ((scalarReductionDerivedExtension l E Y n).obj L))
```

## New

```lean
def finiteArrow
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    Arrow (proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1))) :=
  { left := (pullbackTensorFiniteModel l E Y n).tensor.obj
      ((image (finite l E (n + 1) (Nat.succ_pos n)) c).obj
        ((scalarReductionDerivedExtension l E X n).obj K),
        (scalarReductionDerivedExtension l E Y n).obj L)
    right := (image (finite l E (n + 1) (Nat.succ_pos n)) c).obj
      ((pullbackTensorFiniteModel l E X n).tensor.obj
        ((scalarReductionDerivedExtension l E X n).obj K,
          (pull (finite l E (n + 1) (Nat.succ_pos n)) f).obj
            ((scalarReductionDerivedExtension l E Y n).obj L)))
    hom := finiteReductionProjection l E n c
      ((scalarReductionDerivedExtension l E X n).obj K)
      ((scalarReductionDerivedExtension l E Y n).obj L) }
```

## Users

`tools/downstream.py Sheaf.Paper.ConcreteIntegralProjectionCone --uses finiteArrow` lists only the item itself, with zero downstream importing modules. Unfinished DAG parents still retain the item and its original statement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConcreteIntegralProjectionCone | K2 | Identical endpoint types and actual map; explicit proof unfolding. |

## Status

landed 20261026T023420-L-563644 2026-10-26 (merge of deliver/K2/Sheaf.Paper.ConcreteIntegralProjectionCone)
