# isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj

## Reason
The existing upstream instance proof is completed using the ell-adic localizing adjunction and restriction to bounded constructible objects. Its public statement and instance visibility are unchanged.

## Old
```
instance isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj :
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ g).IsLeftAdjoint := by sorry
```

## New
```
instance isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj :
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ g).IsLeftAdjoint := by
  exact isLeftAdjoint_boundedConstructibleLowerStar_of_ellAdic _ ℓ g .algebraicClosure
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | G2 | Uses the completed instance unchanged. |

## Status
landed 20261017T120638-L-306766 2026-10-17 (merge of deliver/C1/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek)
