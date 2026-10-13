# AlgebraicGeometry.selfTorConormalComparison_unique

## Reason

The proof uses two private proof-only imports: the proved Koszul contraction
formula and finite-free exterior bases. The public import, theorem signature,
visibility and all existing definitions remain unchanged. This record documents
the elaboration environment change flagged by the static delivery check.

## Old

```lean
public import Sheaf.RingTheory.SelfTorConormalComparisonPredicate

theorem selfTorConormalComparison_unique (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ)
    (c d : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)))
    (hc : IsSelfTorConormalComparison A I n c)
    (hd : IsSelfTorConormalComparison A I n d) : c = d
```

## New

```lean
public import Sheaf.RingTheory.SelfTorConormalComparisonPredicate
import Sheaf.RingTheory.KoszulGeneratorChainMap
import Mathlib.LinearAlgebra.ExteriorPower.Basis

theorem selfTorConormalComparison_unique (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ)
    (c d : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)))
    (hc : IsSelfTorConormalComparison A I n c)
    (hd : IsSelfTorConormalComparison A I n d) : c = d
```

Only the theorem proof changes; the added helper is private and fully proved.
No target statement or definition changes, and no consumer adaptation is required.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.SelfTorConormalComparison | unclaimed | Sole direct importer; the theorem has the identical signature and visibility. |

## Status

landed 20261013T215558-L-895423 2026-10-13 (merge of deliver/C4/Sheaf.RingTheory.SelfTorConormalComparisonUnique)
