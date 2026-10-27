# Explicit comparison types and scalar-square condition reuse

## Reason

Delivery path: `coord/changes/completed-pullback-tensor-explicit-types.md`.
This record is included directly in the repaired J6 packet; it needs no
reviewer-side basename fix. Returned head: `0a67bf11053`.

The full original module and proof update repeatedly exceed the 60-second compile
limit. Supplying the existing type of the mapping-cocone lift explicitly prevents
inference from repeatedly expanding the coefficient records. The two scalar-square
condition definitions use `type_of%` to reuse their preceding theorem's exact elaborated
statement rather than elaborating the same long equality again. These are definitionally
identical propositions; no theorem statement, comparison value or target meaning changes.
The Roos lift binds the existing abelian and countable-product structures locally,
without changing either structure. The default elaboration transparency now respects definition boundaries. Six existing
bodies locally restore permissive conversion without changing their terms or signatures.
Local irreducibility of `HasDerivedCategory.standard`, `Functor.leftAdjoint` and
`Functor.mapDerivedCategory` affects only elaboration inside this module.

## Old

```lean
def pullbackTensorRoosUnit (W : Scheme.{u})
    (P : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P).obj (op n))
      (integralOperationsTowerStep
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P)))
    (pullbackTensorRoosAugmentation l E W P) 0
    (pullbackTensorRoosAugmentation_condition l E W P)
```

```lean
def canonicalIntegralPullbackTensor_scalar_condition {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :=
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι X).map ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
      (integralTensorScalarComparison l E L ι X
        (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
        (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom ≫
      ((@constructibleIntegralTensor l _ L _ _ _ X hX)).map
        (Prod.mkHom (integralPullbackScalarComparison l E L ι f M).hom
          (integralPullbackScalarComparison l E L ι f N).hom) =
    (integralPullbackScalarComparison l E L ι f
      (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M,N))).hom ≫
      ((@constructibleIntegralPullback l _ L _ _ _ X Y f hX hY)).map
        (integralTensorScalarComparison l E L ι Y M N).hom ≫
      ((@canonicalIntegralPullbackTensor l _ L _ _ _ X Y f hX hY)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj M)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj N)).hom
```

```lean
def canonicalRationalPullbackTensor_scalar_condition {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfRationalConstructibleCategory l E Y) :=
    (sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
      (rationalTensorScalarComparison l E L ι X).hom.app
        (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M,((@rationalDerivedPullback l _ E
          _ _ _ X Y f hX hY)).obj N) ≫
      ((@rationalDerivedTensor l _ L _ _ _ X hX)).map
        (Prod.mkHom ((rationalPullbackScalarComparison l E L ι f).hom.app M)
          ((rationalPullbackScalarComparison l E L ι f).hom.app N)) =
    (rationalPullbackScalarComparison l E L ι f).hom.app
      (((@rationalDerivedTensor l _ E _ _ _ Y hY)).obj (M,N)) ≫
      ((@rationalDerivedPullback l _ L _ _ _ X Y f hX hY)).map
        ((rationalTensorScalarComparison l E L ι Y).hom.app (M,N)) ≫
      ((@canonicalRationalPullbackTensor l _ L _ _ _ X Y f hX hY)
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj N)).hom
end ScalarCompatibility
```

## New

```lean
def pullbackTensorRoosUnit (W : Scheme.{u})
    (P : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :
    ((pullbackTensorConstantLimit l E W).mapHomologicalComplex (.up ℤ)).obj P ⟶
      integralOperationsRoos
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P) :=
  letI : Abelian (integralTowerModules l E W) := inferInstance
  letI : HasCountableProducts (integralTowerModules l E W) := inferInstance
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P).obj (op n))
      (integralOperationsTowerStep
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P)))
    (pullbackTensorRoosAugmentation l E W P) 0
    (pullbackTensorRoosAugmentation_condition l E W P)
```

```lean
def canonicalIntegralPullbackTensor_scalar_condition {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) : Prop :=
  type_of% (canonicalIntegralPullbackTensor_scalar l E L ι f M N)
```

```lean
def canonicalRationalPullbackTensor_scalar_condition {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfRationalConstructibleCategory l E Y) : Prop :=
  type_of% (canonicalRationalPullbackTensor_scalar l E L ι f M N)
```

## Users

The downstream declaration scan was run for all three names. `pullbackTensorRoosUnit`
has only the item module as a textual consumer. The two condition definitions have the
same four consumers. Their types and values are definitionally identical, so no consumer
adaptation is required.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.CompletedPullbackTensorComparison` | J6 | Explicit existing type and identical proposition aliases. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | F7 | Both scalar-square condition propositions unchanged. |
| `Sheaf.Paper.DerivedPullbackTensorIso` | P4 | Both scalar-square condition propositions unchanged. |
| `Sheaf.Paper.SfCoefficientComparisonConclusions` | unclaimed | Both scalar-square condition propositions unchanged. |

## Status

landed 20261025T163731-L-806478 2026-10-25 (merge of deliver/J6/Sheaf.Paper.CompletedPullbackTensorComparison)
