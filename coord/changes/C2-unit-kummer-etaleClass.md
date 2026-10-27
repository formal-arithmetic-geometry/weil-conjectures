# AlgebraicGeometry.Scheme.UnitKummer.etaleClass

## Reason

Reuse the existing relative Kummer construction, definitionally the same boundary followed by scalar insertion. This avoids reconstructing its large concrete cohomology instance terms. Every target and theorem retains its original meaning. This is an interface/performance repair in the assigned Sheaf module; no adopted source-library declaration changes.

## Old

```lean
@[irreducible] def etaleClass (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (u : Γ(X, ⊤)ˣ) :=
  Sheaf.H.map (Etale.ordinaryFiniteRootMap A m hA X) 1
    (X.kummerδ₀ m hX (Additive.ofMul u))
```

## New

```lean
@[irreducible] def etaleClass (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (u : Γ(X, ⊤)ˣ) :
    Sheaf.H (etaleLine A m hA X) 1 :=
  Etale.relativeKummerClass A m hA X hX u
```

## Users

`python3 tools/downstream.py Sheaf.Paper.UnitKummerTwoSiteNormalization --uses etaleClass`
reports no downstream modules and only the item itself as a textual user. The normalization and frame-normalization statements still elaborate in this packet. No target statement changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.UnitKummerTwoSiteNormalization | C2 | Same objects and maps; statements retain their original meaning. |

## Status

landed 20261025T201523-L-2560006 2026-10-25 (merge of deliver/C2/Sheaf.Paper.UnitKummerTwoSiteNormalization)
