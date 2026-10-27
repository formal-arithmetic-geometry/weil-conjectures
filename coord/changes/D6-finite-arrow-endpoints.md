# WeilConjectures.ConcreteIntegralProjection.finiteArrow

## Reason

The endpoint fields previously inherited a large curried proper/open functor
expression through the inferred type of finiteReductionProjection. Specify those
same source and target objects in Arrow.mk. The hom field stays the actual finite
projection, and both endpoint annotations are definitionally the original objects.
This avoids repeatedly elaborating the curried functor type in comparison proofs.

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
  Arrow.mk
    (X := (pullbackTensorFiniteModel l E Y n).tensor.obj
      ((image (finite l E (n + 1) (Nat.succ_pos n)) c).obj
        ((scalarReductionDerivedExtension l E X n).obj K),
        (scalarReductionDerivedExtension l E Y n).obj L))
    (Y := (image (finite l E (n + 1) (Nat.succ_pos n)) c).obj
      ((pullbackTensorFiniteModel l E X n).tensor.obj
        ((scalarReductionDerivedExtension l E X n).obj K,
          (pull (finite l E (n + 1) (Nat.succ_pos n)) f).obj
            ((scalarReductionDerivedExtension l E Y n).obj L))))
    (finiteReductionProjection l E n c
    ((scalarReductionDerivedExtension l E X n).obj K)
    ((scalarReductionDerivedExtension l E Y n).obj L))
```

## Users

`tools/downstream.py Sheaf.Paper.ConcreteIntegralProjectionCone --uses finiteArrow`
finds only the item itself (10 occurrences). The only module importing the item,
`Sheaf.Paper.ConcreteProjectionFieldDescent`, does not name the definition.
The endpoint objects and actual finite morphism are identical; the inferred arrow
type is unchanged. No statement becomes stronger or weaker.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConcreteIntegralProjectionCone | D6 | Explicit, definitionally identical endpoints. |

## Status

landed 20261025T201631-L-2591332 2026-10-25 (merge of deliver/D6/Sheaf.Paper.ConcreteIntegralProjectionCone)
