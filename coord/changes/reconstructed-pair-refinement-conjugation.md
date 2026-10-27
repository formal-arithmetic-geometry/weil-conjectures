# WeilConjectures.ReconstructedPairRefinement.systemDown

## Reason

Kernel conversion of the expanded coordinate conjugation times out when proving
`systemDown_isIso`. Factor its identical five-factor expression through the generic
public irreducible `conjugate` and `conjugateComponent` definitions. Unfolding them
gives the original component formula; naturality is proved using the original
composite. No hypotheses, maps, comparison
normalizations or coordinate choices change. The generic invertibility theorem now
checks against abstract categories before specialization.

## Old

```lean
def systemDown {c d : Compactification f}
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d) :
    D₂.transport.compact.functor ⟶ D₁.transport.compact.functor :=
  Functor.whiskerRight (coordinates l E X.scheme).counitIso.inv
      D₂.transport.compact.functor ≫
    Functor.whiskerLeft (coordinates l E X.scheme).inverse
      (beta l E D₂.strict D₂.brown D₂.finite D₂.transport).hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (coordinates l E X.scheme).inverse
        (systemRefinement l E k X Y f w)) (coordinates l E Y.scheme).functor ≫
    Functor.whiskerLeft (coordinates l E X.scheme).inverse
      (beta l E D₁.strict D₁.brown D₁.finite D₁.transport).inv ≫
    Functor.whiskerRight (coordinates l E X.scheme).counitIso.hom
      D₁.transport.compact.functor
```

## New

```lean
def systemDown {c d : Compactification f}
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d) :
    D₂.transport.compact.functor ⟶ D₁.transport.compact.functor :=
  conjugate (coordinates l E X.scheme) (coordinates l E Y.scheme).functor
    D₂.transport.compact.functor D₁.transport.compact.functor
    (systemSupport l E d) (systemSupport l E c)
    (beta l E D₂.strict D₂.brown D₂.finite D₂.transport)
    (beta l E D₁.strict D₁.brown D₁.finite D₁.transport)
    (systemRefinement l E k X Y f w)
```

The new public irreducible definitions `conjugateComponent` and `conjugate`,
immediately before `systemDown`, record the old five-factor formula with its
coordinate equivalence, realization functor, two support functors, two comparison
isomorphisms and middle transformation as explicit parameters. `conjugate` records
its component through `conjugateComponent`; its naturality is the naturality of
the original functor-category composite. Both are real constructions with no holes.
Unfolding their bodies yields the original component formula. Naturality proofs
are equal by proof irrelevance, so the same natural transformation is retained.
The full item compiled in 33.7 seconds after this refactor.

## Users

`python3 tools/downstream.py Sheaf.Paper.ReconstructedPairRefinementCoherence
--uses systemDown` reports zero downstream modules and the item itself as the sole
textual consumer (seven occurrences before this change). No target statement uses
this definition through an existing import. The node's planned parent dependencies
are preserved, and the formula they will use has identical meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | Z9 | Same five-factor map; generic conjugation API supplies its invertibility proof. |

## Status

landed 20261025T165020-L-1160155 2026-10-25 (merge of deliver/Z9/Sheaf.Paper.ReconstructedPairRefinementCoherence)
