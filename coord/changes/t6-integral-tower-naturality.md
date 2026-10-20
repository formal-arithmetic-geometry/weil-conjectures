# integralReductionTowerMap_naturality

## Reason

The completeness conclusion of normalizedDVRTower_effectivity uses the canonical
augmented integral reduction tower. Its naturality proof is still a hole in the
finite-field interface. The unrestricted canonical interface already contains the
pure-tensor argument; specialize the same argument to the published finite-field
maps. This closes that dependency without changing a statement or definition.

## Old

```lean
theorem integralReductionTowerMap_naturality
    {P K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (i j : ℕᵒᵖ) (f : i ⟶ j) :
    ((Functor.const ℕᵒᵖ).obj (DerivedCategory.Q.obj K)).map f ≫
        integralReductionTowerMap l E Y D hl q hq j.unop =
      integralReductionTowerMap l E Y D hl q hq i.unop ≫
        (integralReductionTower l E Y D hl P).map f := by
  sorry
```

## New

The signature above is unchanged. In the proof, the two pure-tensor conditions give
unit_(n+1) followed by transition_n = unit_n, since the quotient sends 1 to 1.
Localize this equality, prepend the inverse resolution map, and use
NatTrans.ofOpSequence. Naturality of that natural transformation gives every arrow.
The complete proof is in lean/Sheaf/Paper/IntegralReductionTower.lean.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralReductionTower | unclaimed | Its cone uses the naturality theorem; signature and cone construction stay identical. |
| Sheaf.Paper.NormalizedDVREffectivity | T6 | Uses the canonical augmented tower in its completeness conclusion. |

The direct declaration-use search reports IntegralReductionTower itself. Indirect
importers need no adaptation: all public signatures, definitions and imports stay
identical. This delivery changes only the theorem proof and local proof elaboration
attributes in that module. No module held by another group is adapted.

## Status

landed 20261020T211832-L-3509084 2026-10-20 (merge of deliver/T6/Sheaf.Paper.NormalizedDVREffectivity)
