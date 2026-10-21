# AlgebraicGeometry.surjective_stalk_homology_of_perfect_local_unit

## Reason

Restore the module recorded by `lem-sc-perfect-local-degree-zero-unit` from
`quarantine/Sheaf/AlgebraicGeometry/PerfectLocalDegreeZeroUnit.lean`, as required by
`coord/rework.tsv`. Its old public `Sheaf.AlgebraicGeometry.DerivedPullback` import is
now an empty withdrawn shim. Import the adopted canonical declaration from
`WeilConjectures.AlgebraicGeometry.DerivedPullback` instead. The theorem's binders,
universes and conclusion are unchanged. Explicit evaluation additivity fixes the
negative-Betti calculation without changing the mathematical route.

## Old

The quarantined file used:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

Its theorem signature was:

```lean
theorem surjective_stalk_homology_of_perfect_local_unit (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ x : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField x)).toRingedSpace))]
    (K : schemeDerivedCategory S) (hK : Scheme.IsPerfect S K)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ K) (s : S)
    (hnegative : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
        ((derivedPullback (S.fromSpecResidueField s)).obj K)))
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map a))) :
    Function.Surjective (Scheme.Modules.Hom.stalkLinearMap
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map a) s)
```

## New

The restored file uses:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

The theorem signature remains verbatim:

```lean
theorem surjective_stalk_homology_of_perfect_local_unit (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ x : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField x)).toRingedSpace))]
    (K : schemeDerivedCategory S) (hK : Scheme.IsPerfect S K)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ K) (s : S)
    (hnegative : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
        ((derivedPullback (S.fromSpecResidueField s)).obj K)))
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map a))) :
    Function.Surjective (Scheme.Modules.Hom.stalkLinearMap
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map a) s)
```

## Users

`tools/downstream.py` reports the item as unknown because it is quarantined. A
search of current and quarantined Lean files, plus all DAG dependency and proof-step
references, finds one consumer. Its application supplies precisely the unchanged
perfectness, negative-fibre-vanishing and degree-zero-residue-isomorphism hypotheses.
No definition or target statement changes, so target semantic review is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | quarantined, unchanged | The application at the fixed point has the identical type; no adaptation required. |

## Status

landed 20261021T002147-L-1493591 2026-10-21 (merge of deliver/N3/Sheaf.AlgebraicGeometry.PerfectLocalDegreeZeroUnit)
