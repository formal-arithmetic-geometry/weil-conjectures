# AlgebraicGeometry.ProEtale.supportedCoefficientTensorDerivedHom

## Reason

The derived comparison family repeatedly expanded the specialized monoidal derived category. Apply the generic ComparisonHom to the same three exact functors. The upstream derivedTensor is curriedTensor, so the displayed tensor object and every component remain the same.

All changes are in the Y3 item. No adopted source-library file or target signature changes.
The two generic result modules are fully proved; no object is chosen from an unproved existence.
Definitions used by reachable targets should receive the usual semantic re-review: the equations
and their maps are preserved, with no added assumptions or weakened normalization.

## Old

```lean
noncomputable def supportedCoefficientTensorDerivedHom
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)] :
    Type (u + 2) :=
    ∀ M N : DerivedCategory (ModuleCat.{u + 1} A),
      (supportedCoefficients A (Etale.supportedProductImmersion f g i j)).mapDerivedCategory.obj
          (M ⊗ N) ⟶
        ((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).obj
          ((supportedFirstCoefficients A f g i).mapDerivedCategory.obj M)).obj
          ((supportedSecondCoefficients A f g j).mapDerivedCategory.obj N)
```

## New

```lean
noncomputable def supportedCoefficientTensorDerivedHom
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)] :
    Type (u + 2) :=
  SupportedTensorDerivation.ComparisonHom
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct --uses supportedCoefficientTensorDerivedHom`
finds only the item itself as a direct symbol user. The full downstream module list is also included.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct | Y3 | Same map and equations through shared generic interfaces; all proofs completed. |
| Sheaf.AlgebraicGeometry.SupportQuotientProduct | X2 | No direct use of this symbol; its imported supported product has the same meaning. |
| Sheaf.AlgebraicGeometry.SupportedProductQuotientModel | unclaimed | No direct use of this symbol; its imported supported product has the same meaning. |
| Sheaf.Paper.SupportedHomAdjunctionTranspose | unclaimed | No direct use of this symbol; its imported supported product has the same meaning. |

No consumer adaptation is required. The delivery compiles the original consumers against the repaired item.

## Status

landed 20261020T233240-L-911048 2026-10-20 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct)
