# affineBaseChangeTildeRepresentativeIso

## Reason

The new identity-representative calculation needs the explicit representative construction.
Move the unchanged definition into an independent module to avoid a cycle when the original
module imports that calculation. Its type, value and public visibility are unchanged.

## Old

```lean
def affineBaseChangeTildeRepresentativeIso
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    DerivedCategory.Q.obj (((affineTildeFunctor A').mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) ≅
      (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj K
```

The definition was in `Sheaf.Algebra.Homology.AffineBaseChangeTildeMateFactorization`.

## New

```lean
def affineBaseChangeTildeRepresentativeIso
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    DerivedCategory.Q.obj (((affineTildeFunctor A').mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) ≅
      (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj K
```

The identical definition is in `Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative`,
publicly imported by its old module. Added a proved hom-composition equation there.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.AffineBaseChangeTildeMateFactorization | F1 | imports the new definition module publicly |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeOrdinaryComparison | unclaimed | definition and target remain visible with identical signatures; no adaptation |

There are no adapted existing modules besides the item. The downstream tool found only the
item and OrdinaryComparison as textual users of the moved definition. All transitive importers
continue to see it through the unchanged public declaration name.

## Status

landed 20261014T025137-L-156195 2026-10-14 (merge of deliver/F1/Sheaf.Algebra.Homology.AffineBaseChangeTildeMateFactorization)
