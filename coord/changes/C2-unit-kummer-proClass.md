# AlgebraicGeometry.Scheme.UnitKummer.proClass

## Reason

Write the previously inferred result type explicitly, preserving the exact type and body. This keeps elaboration of the large sheaf cohomology instances predictable. Every target and theorem retains its original meaning. This is an interface/performance repair in the assigned Sheaf module; no adopted source-library declaration changes.

## Old

```lean
@[irreducible] def proClass (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤)))
    (u : Γ(X, ⊤)ˣ) :=
  Sheaf.H.map ((ProEtale.cartierRootsIso X m hm hX).hom ≫ proInsertion A m hm hA X) 1
    (comparisonCohomologyMap X (X.rootsOfUnitySheaf m) 1
      (X.kummerδ₀ m hX (Additive.ofMul u)))
```

## New

```lean
@[irreducible] def proClass (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤)))
    (u : Γ(X, ⊤)ˣ) : Sheaf.H (proLine A m hm hA X) 1 :=
  Sheaf.H.map
    ((ProEtale.cartierRootsIso X m hm hX).hom ≫ proInsertion A m hm hA X) 1
    (comparisonCohomologyMap X (X.rootsOfUnitySheaf m) 1
      (X.kummerδ₀ m hX (Additive.ofMul u)))
```

## Users

`python3 tools/downstream.py Sheaf.Paper.UnitKummerTwoSiteNormalization --uses proClass`
reports no downstream modules and only the item itself as a textual user. The normalization and frame-normalization statements still elaborate in this packet. No target statement changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.UnitKummerTwoSiteNormalization | C2 | Same objects and maps; statements retain their original meaning. |

## Status

landed 20261025T201523-L-2560006 2026-10-25 (merge of deliver/C2/Sheaf.Paper.UnitKummerTwoSiteNormalization)
