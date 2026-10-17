# isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj

## Reason
The existing upstream instance proof is completed using the ell-adic localizing adjunction and restriction to bounded constructible objects. Its public statement and instance visibility are unchanged.

## Old
```
instance isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructibleLowerStar (Profinite.padicIntegersRingObj ℓ E) ℓ g).IsLeftAdjoint := by sorry
```

## New
```
instance isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructibleLowerStar (Profinite.padicIntegersRingObj ℓ E) ℓ g).IsLeftAdjoint := by
  exact isLeftAdjoint_boundedConstructibleLowerStar_of_ellAdic _ ℓ g (.integral E)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | G2 | Uses the completed instance unchanged. |

## Status
landed 20261017T120638-L-306766 2026-10-17 (merge of deliver/C1/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek)
