# AlgebraicGeometry.Scheme.UnitKummer.frameAbelianClass

## Reason

Use the existing mapExtComp API for the same exact-functor action and integer-generator precomposition. This keeps the large Ext instances abstract; no object, generator or class changes. Every target and theorem retains its original meaning. This is an interface/performance repair in the assigned Sheaf module; no adopted source-library declaration changes.

## Old

```lean
@[irreducible] def frameAbelianClass (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (u : Γ(X, ⊤)ˣ) :
    Sheaf.H ((forgetPro P.Coefficient X).obj (P.frameTwist X 1)) 1 :=
  letI : (forgetPro P.Coefficient X).IsLeftAdjoint :=
    (Sheaf.forget₂CoinduceAdj (ProEt.topology X) P.Coefficient).isLeftAdjoint
  (Abelian.Ext.mk₀ (frameIntegralGenerator P X)).comp
    ((P.frameKummer X a u).mapExactFunctor (forgetPro P.Coefficient X)) (zero_add 1)
```

## New

```lean
@[irreducible] def frameAbelianClass (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (u : Γ(X, ⊤)ˣ) :
    Sheaf.H ((forgetPro P.Coefficient X).obj (P.frameTwist X 1)) 1 :=
  letI : (forgetPro P.Coefficient X).IsLeftAdjoint :=
    (Sheaf.forget₂CoinduceAdj (ProEt.topology X) P.Coefficient).isLeftAdjoint
  (forgetPro P.Coefficient X).mapExtComp (frameIntegralGenerator P X)
    (P.frameTwist X 1) 1 (P.frameKummer X a u)
```

## Users

`python3 tools/downstream.py Sheaf.Paper.UnitKummerTwoSiteNormalization --uses frameAbelianClass`
reports no downstream modules and only the item itself as a textual user. The normalization and frame-normalization statements still elaborate in this packet. No target statement changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.UnitKummerTwoSiteNormalization | C2 | Same objects and maps; statements retain their original meaning. |

## Status

landed 20261025T201523-L-2560006 2026-10-25 (merge of deliver/C2/Sheaf.Paper.UnitKummerTwoSiteNormalization)
