# AlgebraicGeometry.ProEtale.supportedCoefficientTensorDerivedCondition

## Reason

The normalization repeatedly compared the tensorObj and cochain monoidal presentations while checking the chosen complex map. Use ComparisonFamilyCondition whose complex family has the shared ComplexHom type. It retains the original curried-tensor morphism composition and the final Q.map(eqToHom(...)) identifying the monoidal complex tensor with the signed total complex. The generic proof explicitly uses tensorHom_def and the fact that this last map is an identity; neither normalization component is dropped from the condition. The generic interface keeps the actual chosen coefficient comparison as its parameter.

All changes are in the Y3 item. No adopted source-library file or target signature changes.
The two generic result modules are fully proved; no object is chosen from an unproved existence.
Definitions used by reachable targets should receive the usual semantic re-review: the equations
and their maps are preserved, with no added assumptions or weakened normalization.

## Old

```lean
noncomputable def supportedCoefficientTensorDerivedCondition
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    (t : supportedCoefficientTensorDerivedHom A f g i j) : Prop :=
      (∀ (M M' N N' : DerivedCategory (ModuleCat.{u + 1} A))
        (a : M ⟶ M') (b : N ⟶ N'),
        (supportedCoefficients A (Etale.supportedProductImmersion f g i j)).mapDerivedCategory.map
            (a ⊗ₘ b) ≫ t M' N' = t M N ≫
          supportedDerivedTensorMap A (pullback f g)
            ((supportedFirstCoefficients A f g i).mapDerivedCategory.map a)
            ((supportedSecondCoefficients A f g j).mapDerivedCategory.map b)) ∧
      (∀ P Q : CochainComplex (ModuleCat.{u + 1} A) ℤ,
        (supportedCoefficients A (Etale.supportedProductImmersion f g i j)).mapDerivedCategory.map
            (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          (supportedCoefficients A
            (Etale.supportedProductImmersion f g i j)).mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
          DerivedCategory.Q.map (supportedCoefficientTensorComplex A f g i j P Q) =
        t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
          supportedDerivedTensorMap A (pullback f g)
            ((supportedFirstCoefficients A f g i).mapDerivedCategoryFactors.hom.app P)
            ((supportedSecondCoefficients A f g j).mapDerivedCategoryFactors.hom.app Q) ≫
          supportedDerivedTensorLocalization A (pullback f g)
            (((supportedFirstCoefficients A f g i).mapHomologicalComplex (.up ℤ)).obj P)
            (((supportedSecondCoefficients A f g j).mapHomologicalComplex (.up ℤ)).obj Q))
```

## New

```lean
noncomputable def supportedCoefficientTensorDerivedCondition
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    (t : supportedCoefficientTensorDerivedHom A f g i j) : Prop :=
  SupportedTensorDerivation.ComparisonFamilyCondition
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
    (supportedCoefficientTensorComplex A f g i j) t
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct --uses supportedCoefficientTensorDerivedCondition`
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
