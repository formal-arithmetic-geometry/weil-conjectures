# AlgebraicGeometry.Scheme.IsDerivedTensorAugmentation

## Reason

Retire-first item: the Sheaf module duplicates the official upstream module. Follow the
human-approved retirement instructions in coord/changes/retire-sheaf-twins-20261020.md.
The Sheaf module currently has no importing Lean module. Removing this duplicate avoids
loading two declarations of the same name when other groups switch to the upstream API.

The two augmentation bodies are textually identical after renaming
CochainComplex.IsAcyclicTensorKFlat to CochainComplex.IsKFlatTensor. The two K-flat
predicate bodies are textually identical, including universes and the sheaf tensor.
A sandbox-only Lean check expands the old predicate to its acyclicity quantifier and proves
by rfl that the upstream augmentation is equivalent to it, for arbitrary X, A, I, B and β.
The check compiles in 6.9 seconds, with only propext, Classical.choice and Quot.sound.
No assumptions, representative conditions, augmentations or conclusions change.

## Old

In lean/Sheaf/AlgebraicGeometry/DerivedTensorAugmentation.lean:

```lean
def IsDerivedTensorAugmentation (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (A I B : schemeDerivedCategory X) (β : B ⟶ A) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := (SheafOfModules.tensorClosed X.sheaf).1.some
  ∃ P J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P ∧
    CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) J ∧
    ∃ (eA : DerivedCategory.Q.obj P ≅ A) (_eI : DerivedCategory.Q.obj J ≅ I)
      (eB : DerivedCategory.Q.obj (CochainComplex.mapBifunctor P J (curriedTensor _)) ≅ B)
      (u : J ⟶ HomologicalComplex.tensorUnit
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)),
      β = eB.inv ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _) (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map (HomologicalComplex.rightUnitor P).hom ≫ eA.hom

```

## New

Withdraw the Sheaf module using deleted.txt. Point def-sc-derived-tensor-augmentation at
the existing declaration in lean/WeilConjectures/AlgebraicGeometry/DerivedTensorAugmentation.lean:

```lean
def IsDerivedTensorAugmentation (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (A I B : schemeDerivedCategory X) (β : B ⟶ A) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := (SheafOfModules.tensorClosed X.sheaf).1.some
  ∃ P J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    CochainComplex.IsKFlatTensor (R := X.sheaf) P ∧
    CochainComplex.IsKFlatTensor (R := X.sheaf) J ∧
    ∃ (eA : DerivedCategory.Q.obj P ≅ A) (_eI : DerivedCategory.Q.obj J ≅ I)
      (eB : DerivedCategory.Q.obj (CochainComplex.mapBifunctor P J (curriedTensor _)) ≅ B)
      (u : J ⟶ HomologicalComplex.tensorUnit
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)),
      β = eB.inv ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _) (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map (HomologicalComplex.rightUnitor P).hom ≫ eA.hom

```

No upstream file or target statement is edited. The node statement and its dependencies
remain unchanged; only the Lean attachment changes to the official module.

## Users

| module | group holding it | effect |
|---|---|---|
| No Lean consumers of the retired module | none | No adaptation required. |

A complete import/name search of lean/Sheaf and lean/WeilConjectures found zero imports
of the Sheaf copy. Existing upstream consumers already import the official twin and
continue to use the same upstream declaration. The sole DAG attachment to the copy,
def-sc-derived-tensor-augmentation, is redirected in this packet. There are no forced
adaptations and no target-definition review is reopened: the proposition is identical.

## Status

landed 20261020T145531-L-2408249 2026-10-20 (merge of deliver/N2/Sheaf.AlgebraicGeometry.DerivedTensorAugmentation)
