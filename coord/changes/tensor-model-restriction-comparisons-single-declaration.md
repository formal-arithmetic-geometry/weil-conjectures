# AlgebraicGeometry.Scheme.exists_tensorModel_restriction_comparisons

## Reason

The 2026-10-20 upstream sync adopted a complete proof of this theorem with the
same public name. The Sheaf copy still redeclared that name with the
`IsAcyclicTensorKFlat` spelling. Importing both copies can cause duplicate
environment errors; the existing import-only rework leaves this duplication.
The source predicate `IsKFlatTensor` and the Sheaf predicate
`IsAcyclicTensorKFlat` have identical bodies, including the tensor convention.
There is no mathematical difference or hypothesis change.

## Old

The Sheaf module declared the following theorem and its private categorical
transport helper, with a separate copy of the proof:

```lean
theorem exists_tensorModel_restriction_comparisons
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (A : schemeDerivedCategory X)
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P)
    (eA : DerivedCategory.Q.obj P ≅ A) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    let H := fun E ↦ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf).obj (op A, E)
    let B := fun J ↦ DerivedCategory.Q.obj
      (CochainComplex.mapBifunctor P J (curriedTensor _))
    let HU := derivedInternalHom (Opens.grothendieckTopology U.toScheme.toRingedSpace)
      U.toScheme.toRingedSpace.sheaf
    ∃ (c : ∀ J, B J ≅ DerivedCategory.Q.obj J ⊗ A)
      (d : ∀ J, R.obj (B J) ≅ R.obj (DerivedCategory.Q.obj J) ⊗ R.obj A)
      (h : ∀ E, R.obj (H E) ≅ HU.obj (op (R.obj A), R.obj E)),
      (∀ J J' (u : J ⟶ J'),
        R.map (DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _)
            (ComplexShape.up ℤ))) ≫ (d J').hom =
          (d J).hom ≫ (R.map (DerivedCategory.Q.map u) ⊗ₘ 𝟙 (R.obj A))) ∧
      (∀ J E (ξ : DerivedCategory.Q.obj J ⟶ H E),
        (d J).hom ≫ schemeDerivedTensorHomEquiv U.toScheme
          (R.obj (DerivedCategory.Q.obj J)) (R.obj A) (R.obj E)
          (R.map ξ ≫ (h E).hom) =
        R.map ((c J).hom ≫ schemeDerivedTensorHomEquiv X
          (DerivedCategory.Q.obj J) A E ξ))
```

## New

The Sheaf module publicly re-exports
`WeilConjectures.AlgebraicGeometry.TensorModelRestrictionComparisons` and retains
its existing public KFlat and CanonicalDerivedTensorHom imports. It introduces
no declaration. The node attaches to this existing upstream declaration:

```lean
theorem exists_tensorModel_restriction_comparisons
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (A : schemeDerivedCategory X)
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (eA : DerivedCategory.Q.obj P ≅ A) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    let H := fun E ↦ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf).obj (op A, E)
    let B := fun J ↦ DerivedCategory.Q.obj
      (CochainComplex.mapBifunctor P J (curriedTensor _))
    let HU := derivedInternalHom (Opens.grothendieckTopology U.toScheme.toRingedSpace)
      U.toScheme.toRingedSpace.sheaf
    ∃ (c : ∀ J, B J ≅ DerivedCategory.Q.obj J ⊗ A)
      (d : ∀ J, R.obj (B J) ≅ R.obj (DerivedCategory.Q.obj J) ⊗ R.obj A)
      (h : ∀ E, R.obj (H E) ≅ HU.obj (op (R.obj A), R.obj E)),
      (∀ J J' (u : J ⟶ J'),
        R.map (DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _)
            (ComplexShape.up ℤ))) ≫ (d J').hom =
          (d J).hom ≫ (R.map (DerivedCategory.Q.map u) ⊗ₘ 𝟙 (R.obj A))) ∧
      (∀ J E (ξ : DerivedCategory.Q.obj J ⟶ H E),
        (d J).hom ≫ schemeDerivedTensorHomEquiv U.toScheme
          (R.obj (DerivedCategory.Q.obj J)) (R.obj A) (R.obj E)
          (R.map ξ ≫ (h E).hom) =
        R.map ((c J).hom ≫ schemeDerivedTensorHomEquiv X
          (DerivedCategory.Q.obj J) A E ξ))
```

A scratch example with the entire old statement is proved by
`exact exists_tensorModel_restriction_comparisons X U A P hP eA` after importing
both module paths. Thus Lean checks definitional equality of the whole previous
API, not only an implication between the two predicates. The adopted theorem's
axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. No upstream file
or declaration is edited. The same abstract transport proof and all three
mathematical proof dependencies are retained upstream.

## Users

`tools/downstream.py` reports zero live downstream modules. The quarantine and
DAG were checked separately; the parent node still uses this theorem.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons | D4 | Re-exports the existing theorem at the same definitionally equal type. |
| Sheaf.AlgebraicGeometry.TensorModelRestrictionAdjunction | unclaimed, quarantined | Its call `exists_tensorModel_restriction_comparisons X U A P hP eA` remains valid at the old predicate spelling, as checked by the full-type compatibility example. Its archive and DAG attachment are preserved. |
| Sheaf.AlgebraicGeometry.TensorRoofTransposition | unclaimed, quarantined | Indirect user through the adjunction module; no theorem type changes. Its archive and DAG attachment are preserved. |
| WeilConjectures.AlgebraicGeometry.TensorModelRestrictionAdjunction | unclaimed | Already uses the adopted theorem; the Sheaf wrapper now permits both module paths in the same environment. No source change. |

No target signature or definition changes. No forced adaptation is needed.

## Status

landed 20261020T160941-L-3429261 2026-10-20 (merge of deliver/D4/Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons)
